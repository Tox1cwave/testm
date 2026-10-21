#!/usr/bin/env python3
# -*- coding: utf-8 -*-
r"""
AI 代码修复 & 性能优化评测器（单文件，仅依赖 Python 3.8+ 标准库）

出题 + 判卷一体：
  1) python ai_code_bench.py prompt -o prompt.md
       生成题目：规格说明 + 一份充满功能 bug / 安全漏洞 / 隐性问题 / 性能问题的“祖传代码”。
       把 prompt.md 的内容发给被测模型。
  2) 把模型给出的代码保存为 solution.py
       （也可以直接把模型的整段回复存成 .md/.txt，评测器会自动提取 ```python 代码块）。
  3) python ai_code_bench.py judge solution.py [model_b.py ...]
       在子进程中运行候选代码（有超时、崩溃隔离）：
         - 功能测试（固定用例 + 与参考实现随机对拍）
         - 隐性问题测试（修改入参、跨调用状态泄漏、资源泄漏、深递归、边界条件……）
         - 安全测试（代码注入、SQL 注入、路径穿越、符号链接逃逸、DoS……）
         - 大数据量计时：给出每个函数相对原代码的加速倍数，并校验大数据上的输出是否正确
       输出每项未通过的具体原因和总分。

其它：
  python ai_code_bench.py selftest                  评测器自检（参考答案应满分，原代码应在每个任务上暴露问题）
  python ai_code_bench.py judge @baseline @reference 直接评测原代码 / 内置参考答案（用来校准）

常用选项（judge）：
  --quick            小规模、单次计时，快速出结果
  --reps N           每个实现计时 N 轮（默认 3，取中位数）
  --only T1,T3       只评测部分任务
  --report out.md    额外输出 Markdown 报告；--json out.json 输出 JSON
  -v                 显示通过项和候选代码的 stderr 输出

注意：不要把本文件发给被测模型——它包含参考答案和全部隐藏测试。只发 prompt 命令生成的内容。
本评测器面向“正常作答”的模型；候选代码与测试运行在同一子进程中，并不能防御刻意针对评测器的攻击。
"""

import argparse
import ast
import collections
import copy
import functools
import gc
import hashlib
import heapq
import importlib.util
import json
import keyword
import math
import operator
import os
import queue
import random
import re
import shutil
import sqlite3
import statistics
import string
import subprocess
import sys
import tempfile
import threading
import time
import traceback
import types
import unicodedata
import warnings

BENCH_VERSION = "1.0"

# ════════════════════════════════════════════════════════════════════════════
# 第 1 部分：题目 —— 祖传代码
# ════════════════════════════════════════════════════════════════════════════

CHALLENGE_CODE = r'''"""shop_utils.py —— 电商后台工具函数（祖传代码）"""
import os
import sqlite3  # noqa: F401  customer_spend 的 conn 参数是 sqlite3.Connection


def top_skus(orders, k):
    """热销排行：返回销量最高的 k 个 (sku, 总销量)。"""
    skus = []
    for order in orders:
        for item in order["items"]:
            if item["sku"] not in skus:
                skus.append(item["sku"])

    result = []
    for sku in skus:
        total = 0
        for order in orders:
            for item in order["items"]:
                if item["sku"] == sku:
                    total += item["qty"]
        result.append((sku, total))

    # 冒泡排序，销量高的排前面
    for i in range(len(result)):
        for j in range(len(result) - 1 - i):
            if result[j][1] < result[j + 1][1]:
                result[j], result[j + 1] = result[j + 1], result[j]
    return result[:k]


def order_totals(orders, coupons, _cache={}):
    """订单结算：返回 {order_id: 应付金额字符串}。"""
    result = {}
    for order in orders:
        oid = order["order_id"]
        if oid in _cache:  # 缓存一下，避免重复计算
            subtotal = _cache[oid]
        else:
            subtotal = 0.0
            for item in order["items"]:
                subtotal += item["qty"] * float(item["unit_price"])
            _cache[oid] = subtotal
        order["subtotal"] = subtotal  # 顺手记下来，方便排查问题

        discount = 0.0
        code = order.get("coupon")
        if code:
            for c in coupons:
                if c["code"] == code and subtotal > float(c["min_subtotal"]):
                    discount = round(subtotal * c["percent_off"] / 100, 2)
        result[oid] = "%.2f" % (subtotal - discount)
    return result


def eval_rule(expr, variables):
    """定价规则表达式求值，例如 "price * qty - discount"。"""
    for name, value in variables.items():
        expr = expr.replace(name, str(value))
    return eval(expr)


def read_report(base_dir, name):
    """读取 base_dir 下的报表文件，返回文本内容。"""
    if ".." in name:
        raise PermissionError("非法路径: " + name)
    path = os.path.join(base_dir, name)
    folder = os.path.dirname(path)
    if not os.path.isdir(folder) or os.path.basename(path) not in os.listdir(folder):
        raise FileNotFoundError(name)
    f = open(path)
    return f.read()


def find_bursts(events, window, threshold):
    """找出在 window 秒内产生至少 threshold 个事件的用户。"""
    events.sort(key=lambda e: e[1])  # 先按时间排好序
    users = []
    for user, _ in events:
        if user not in users:
            users.append(user)

    bursts = []
    for user in users:
        times = [t for u, t in events if u == user]
        for i in range(len(times)):
            count = 0
            for j in range(i, len(times)):
                if times[j] - times[i] <= window:
                    count += 1
            if count >= threshold:
                bursts.append(user)
                break
    return sorted(bursts)


def customer_spend(conn, names):
    """查询每个客户的消费总额（单位：分）。"""
    result = {}
    for name in names:
        cur = conn.execute(
            "SELECT SUM(amount_cents) FROM orders WHERE customer = '%s'" % name)
        result[name] = cur.fetchone()[0]
    return result


def category_totals(parent_of, sales):
    """类目销量汇总：每个类目 = 自身销量 + 所有子孙类目的销量。"""
    def children(node):
        return [c for c, p in parent_of.items() if p == node]

    def subtotal(node):
        total = sales.get(node, 0)
        for child in children(node):
            total += subtotal(child)
        return total

    return {node: subtotal(node) for node in parent_of}
'''

# ════════════════════════════════════════════════════════════════════════════
# 第 2 部分：题目 —— 发给模型的提示词（规格说明）
# ════════════════════════════════════════════════════════════════════════════

PROMPT_TEMPLATE = r"""# 任务：修复并优化 shop_utils.py

你是一名资深 Python 工程师。下面的 `shop_utils.py` 是某电商后台的工具模块，共 7 个函数。这份“祖传代码”能跑，但问题很多：功能 bug、安全漏洞、隐藏的状态/资源问题，以及严重的性能问题。

请**重写整个模块**：

1. 每个函数都必须严格满足下文【规格说明】。规格与现有代码的行为不一致时，以规格为准。
2. 修复所有安全漏洞和隐性问题（另见【通用约定】）。
3. 在保证正确的前提下尽可能提高性能。评测会在较大规模的数据上计时，并与原代码对比加速倍数。
4. 只能使用 Python 标准库，兼容 Python 3.8 及以上版本。函数名、参数名、参数顺序保持不变；可以新增辅助函数、常量和 import。
5. 输出一个**完整的、可以直接保存为 `solution.py` 的 Python 文件**，放在**一个** ```python 代码块中。代码块之后可以简要列出你发现并修复的问题。

评分方式：先用隐藏测试（含边界条件和恶意输入）检查正确性、安全性和健壮性，再在大数据量下与原代码对比运行时间。结果不正确或存在安全漏洞时，速度再快也不得分。

## 通用约定

- 除非规格另有说明，不得修改任何传入的参数（包括列表的顺序、字典的内容、嵌套对象）。
- 函数的结果只能取决于本次调用的参数（以及文件系统 / 数据库的当前内容），多次调用之间不能相互影响。
- 规格要求抛出的异常必须是指定的类型（或其子类）。
- 性能测试的大致数据规模：<<PERF_SCALE>>

## 规格说明

### 1. `top_skus(orders, k) -> list[tuple[str, int]]` 热销排行

- `orders`：订单列表。每个订单是 dict：`{"order_id": str, "items": [{"sku": str, "qty": int, "unit_price": str}, ...]}`，可能还有可选键 `"coupon"`。`qty` 为非负整数。
- 统计每个 sku 在全部订单中的 `qty` 之和，只保留总和 > 0 的 sku。
- 排序：总和降序；总和相同时按 sku 升序（Python 字符串的默认比较）。
- 返回前 `k` 个 `(sku, 总和)` 元组组成的 list；`k <= 0` 时返回 `[]`；`k` 超过 sku 数量时返回全部。

### 2. `order_totals(orders, coupons) -> dict[str, str]` 订单结算

- `orders` 格式同上，`order_id` 互不相同。`unit_price` 是最多两位小数的非负十进制字符串，如 `"19.99"`、`"5"`、`"0.5"`。订单可能带可选键 `"coupon"`（值为 str 或 None）。
- `coupons`：`[{"code": str, "percent_off": int, "min_subtotal": str}, ...]`。`code` 是互不相同的非空字符串；`0 <= percent_off <= 100`；`min_subtotal` 格式同 `unit_price`。
- 对每个订单：
  - `subtotal = Σ qty × unit_price`，必须精确计算（不允许有浮点误差）。
  - 如果订单的 `coupon` 键存在且不为 None，并且在 `coupons` 中能找到 `code` 与之完全相同（区分大小写）的券，并且 `subtotal >= min_subtotal`，则 `discount = subtotal × percent_off / 100`，按**四舍五入（ROUND_HALF_UP）**保留到 0.01；否则 `discount = 0`。
  - `total = subtotal - discount`。
- 返回 `{order_id: total}`，`total` 是固定两位小数的字符串，如 `"1234.50"`、`"0.00"`（不用科学计数法、不带千分位）。

### 3. `eval_rule(expr, variables) -> int | float` 定价规则表达式

对规则表达式求值。`variables` 为 `{变量名: int 或 float}`（值不会是 bool）。允许的语法（Python 表达式语法的子集）：

- 数字字面量：十进制整数（如 `42`）和十进制小数（如 `3.5`、`.5`、`2.`）；
- 变量名（Python 标识符），取值于 `variables`；
- 二元运算 `+ - * / // %`，一元运算 `+ -`，圆括号；
- 表达式首尾和中间可以有任意空格或制表符。

运算语义（包括结果是 int 还是 float、`/` 为真除法、`//` 与 `%` 的向下取整规则、运算符优先级）必须与 Python 完全一致。

以下情况必须抛出 `ValueError`（不能是其它异常类型，且不能产生任何副作用）：

- 语法错误，或使用了上面没有列出的任何语法：函数调用、属性访问、下标、字符串、`**`、位运算、比较、布尔运算、条件表达式、lambda、`True`/`False`/`None` 等；
- 使用了 `variables` 中不存在的变量名；
- 求值时出现算术错误（除数为 0、结果溢出等）；
- `len(expr) > 200`。

### 4. `read_report(base_dir, name) -> str` 报表读取

读取目录 `base_dir` 下相对路径为 `name` 的文件，返回其文本内容。

- `name` 用 `/` 作分隔符，可以包含子目录，也可以包含 `..`——只要最终路径（解析所有符号链接之后）仍位于 `base_dir`（同样解析符号链接之后）之内即可。
- 先做路径安全检查：如果 `name` 是绝对路径，或者最终路径位于 `base_dir` 之外（包括借助 `..` 或符号链接逃逸），抛出 `PermissionError`。
- 再检查目标：如果目标不存在或不是普通文件（例如是目录），抛出 `FileNotFoundError`。
- 以 UTF-8 解码并**原样**返回全部内容，不做换行符转换（文件中的 `\r\n` 必须原样保留）。
- 打开的文件必须及时关闭。

### 5. `find_bursts(events, window, threshold) -> list[str]` 突发检测

- `events`：`[(user_id: str, timestamp: int), ...]`，顺序任意，同一用户可能有重复的时间戳。`window`、`threshold` 为正整数。
- 如果某用户存在 `threshold` 个事件（时间戳重复的事件分别计数），它们的最大时间戳与最小时间戳之差**严格小于** `window`，该用户就是突发用户。
- 返回所有突发用户的 user_id，升序排列、不重复。

### 6. `customer_spend(conn, names) -> dict[str, int]` 客户消费汇总

- `conn` 是 `sqlite3.Connection`，库中有表 `orders(id INTEGER PRIMARY KEY, customer TEXT NOT NULL, amount_cents INTEGER NOT NULL)`，除主键外没有索引。
- 返回 `{name: 该客户全部订单的 amount_cents 之和}`。`names` 中每个不同的名字都必须出现在结果里，没有订单的为 `0`。
- 名字按完全相等匹配（区分大小写），名字里可能有引号、反斜杠、`%`、`_` 等任意可打印字符。`names` 可能非常长（数万个）。
- 不得修改 `orders` 表的结构或数据，不得关闭连接（可以使用 TEMP 临时表等临时对象）。

### 7. `category_totals(parent_of, sales) -> dict[str, int]` 类目销量汇总

- `parent_of`：`{类目: 父类目或 None}`，描述一个类目森林（None 表示根）。保证所有非 None 的父类目本身也是 `parent_of` 的键。
- `sales`：`{类目: 自身销量(int)}`。不在 `parent_of` 中的键忽略；`parent_of` 中没有销量的类目视为 0。
- 每个类目的汇总销量 = 自身销量 + 所有后代类目的自身销量。返回 `{类目: 汇总销量}`，包含 `parent_of` 中的全部类目。
- 如果父子关系中存在环（包括自己是自己的父类目），抛出 `ValueError`。
- 树的深度可能达到 10 万层，不能因为递归过深而崩溃。

## 原代码（shop_utils.py）

```python
<<CODE>>
```
"""

PERF_SCALE_TEXT = (
    "top_skus 约 5000 个订单 / 1500 种 sku；order_totals 约 1 万个订单 / 3000 张优惠券；"
    "eval_rule 约 2000 次求值（约 200 条不同规则反复出现，每次的 variables 有约 1000 个变量）；"
    "read_report 同一目录约 2500 个文件逐个读取；find_bursts 约 4 万条事件 / 500 个用户；"
    "customer_spend 表约 3 万行、名单约 1200 个名字；category_totals 约 2000 个类目。"
)


def build_prompt():
    return (PROMPT_TEMPLATE.replace("<<PERF_SCALE>>", PERF_SCALE_TEXT)
            .replace("<<CODE>>", CHALLENGE_CODE.strip("\n")))


# ════════════════════════════════════════════════════════════════════════════
# 第 3 部分：参考答案（判卷用的“标准答案”，同时作为性能参照）
# ════════════════════════════════════════════════════════════════════════════

def _ref_top_skus(orders, k):
    if k <= 0:
        return []
    totals = {}
    for order in orders:
        for item in order["items"]:
            sku = item["sku"]
            totals[sku] = totals.get(sku, 0) + item["qty"]
    pairs = [(s, t) for s, t in totals.items() if t > 0]
    key = lambda p: (-p[1], p[0])  # noqa: E731
    if k < len(pairs):
        return heapq.nsmallest(k, pairs, key=key)
    pairs.sort(key=key)
    return pairs


def _ref_price_cents(text):
    """'19.99' -> 1999，'5' -> 500，'0.5' -> 50（整数分，精确）。"""
    whole, _, frac = text.partition(".")
    return int(whole or "0") * 100 + int((frac + "00")[:2])


def _ref_order_totals(orders, coupons):
    table = {c["code"]: c for c in coupons}
    cents_cache = {}
    out = {}
    for order in orders:
        subtotal = 0
        for item in order["items"]:
            price = item["unit_price"]
            cents = cents_cache.get(price)
            if cents is None:
                cents = cents_cache[price] = _ref_price_cents(price)
            subtotal += item["qty"] * cents
        discount = 0
        code = order.get("coupon")
        if code is not None:
            coupon = table.get(code)
            if coupon is not None and subtotal >= _ref_price_cents(coupon["min_subtotal"]):
                # ROUND_HALF_UP(subtotal * p / 100)，非负数时等价于 floor(x + 0.5)
                discount = (2 * subtotal * coupon["percent_off"] + 100) // 200
        total = subtotal - discount
        out[order["order_id"]] = "%d.%02d" % divmod(total, 100)
    return out


_EVAL_BINOPS = {ast.Add: operator.add, ast.Sub: operator.sub, ast.Mult: operator.mul,
                ast.Div: operator.truediv, ast.FloorDiv: operator.floordiv, ast.Mod: operator.mod}
_EVAL_UNOPS = {ast.UAdd: operator.pos, ast.USub: operator.neg}
_EVAL_PLAIN_NODES = (ast.Expression, ast.Name, ast.Load) + tuple(_EVAL_BINOPS) + tuple(_EVAL_UNOPS)


@functools.lru_cache(maxsize=4096)
def _ref_parse_rule(expr):
    try:
        tree = ast.parse(expr.strip(" \t"), mode="eval")
    except (SyntaxError, ValueError, RecursionError, MemoryError):
        raise ValueError("invalid expression") from None
    for node in ast.walk(tree):
        if isinstance(node, ast.Constant):
            if type(node.value) not in (int, float):
                raise ValueError("unsupported literal")
        elif isinstance(node, ast.BinOp):
            if type(node.op) not in _EVAL_BINOPS:
                raise ValueError("unsupported operator")
        elif isinstance(node, ast.UnaryOp):
            if type(node.op) not in _EVAL_UNOPS:
                raise ValueError("unsupported operator")
        elif not isinstance(node, _EVAL_PLAIN_NODES):
            raise ValueError("unsupported syntax: " + type(node).__name__)
    return tree.body


def _ref_eval_node(node, variables):
    if isinstance(node, ast.BinOp):
        left = _ref_eval_node(node.left, variables)
        right = _ref_eval_node(node.right, variables)
        try:
            return _EVAL_BINOPS[type(node.op)](left, right)
        except ArithmeticError:
            raise ValueError("arithmetic error") from None
    if isinstance(node, ast.UnaryOp):
        return _EVAL_UNOPS[type(node.op)](_ref_eval_node(node.operand, variables))
    if isinstance(node, ast.Name):
        try:
            return variables[node.id]
        except KeyError:
            raise ValueError("undefined variable: " + node.id) from None
    return node.value


def _ref_eval_rule(expr, variables):
    if len(expr) > 200:
        raise ValueError("expression too long")
    return _ref_eval_node(_ref_parse_rule(expr), variables)


def _ref_read_report(base_dir, name):
    if os.path.isabs(name) or name.startswith(("/", "\\")):
        raise PermissionError("absolute path is not allowed: %r" % name)
    base = os.path.realpath(base_dir)
    target = os.path.realpath(os.path.join(base, name))
    try:
        inside = os.path.commonpath([base, target]) == base
    except ValueError:
        inside = False
    if not inside:
        raise PermissionError("path escapes base_dir: %r" % name)
    if not os.path.isfile(target):
        raise FileNotFoundError(name)
    with open(target, "r", encoding="utf-8", newline="") as f:
        return f.read()


def _ref_find_bursts(events, window, threshold):
    by_user = {}
    for user, ts in events:
        times = by_user.get(user)
        if times is None:
            by_user[user] = [ts]
        else:
            times.append(ts)
    span = threshold - 1
    out = []
    for user, times in by_user.items():
        if len(times) < threshold:
            continue
        times.sort()
        if any(b - a < window for a, b in zip(times, times[span:])):
            out.append(user)
    out.sort()
    return out


def _ref_customer_spend(conn, names):
    result = dict.fromkeys(names, 0)
    if result:
        for customer, total in conn.execute(
                "SELECT customer, SUM(amount_cents) FROM orders GROUP BY customer"):
            if customer in result:
                result[customer] = total
    return result


def _ref_category_totals(parent_of, sales):
    totals = {node: sales.get(node, 0) for node in parent_of}
    pending = dict.fromkeys(parent_of, 0)  # 尚未汇总进来的子类目数
    for node, parent in parent_of.items():
        if parent is not None:
            pending[parent] += 1
    stack = [node for node, n in pending.items() if n == 0]
    done = 0
    while stack:
        node = stack.pop()
        done += 1
        parent = parent_of[node]
        if parent is not None:
            totals[parent] += totals[node]
            pending[parent] -= 1
            if pending[parent] == 0:
                stack.append(parent)
    if done != len(parent_of):
        raise ValueError("cycle detected in category tree")
    return totals


REFERENCE = {
    "top_skus": _ref_top_skus,
    "order_totals": _ref_order_totals,
    "eval_rule": _ref_eval_rule,
    "read_report": _ref_read_report,
    "find_bursts": _ref_find_bursts,
    "customer_spend": _ref_customer_spend,
    "category_totals": _ref_category_totals,
}

# ════════════════════════════════════════════════════════════════════════════
# 第 4 部分：判卷工具函数
# ════════════════════════════════════════════════════════════════════════════

REF = object()  # 期望值标记：以参考答案的结果为准


def _V(value):
    return ("value", value)


def _E(exc_type):
    return ("raises", exc_type)


def _kind(x):
    if x is None:
        return "None"
    if isinstance(x, bool):
        return "bool"
    if isinstance(x, int):
        return "int"
    if isinstance(x, float):
        return "float"
    if isinstance(x, str):
        return "str"
    if isinstance(x, tuple):
        return "tuple"
    if isinstance(x, list):
        return "list"
    if isinstance(x, dict):
        return "dict"
    return "other:" + type(x).__name__


def _same(a, b):
    """严格比较：类型类别必须一致（int/float/str/tuple/list/dict 互不相同），值必须相等。"""
    ka, kb = _kind(a), _kind(b)
    if ka != kb:
        return False
    if ka in ("tuple", "list"):
        return len(a) == len(b) and all(_same(x, y) for x, y in zip(a, b))
    if ka == "dict":
        if len(a) != len(b):
            return False
        for key, va in a.items():
            if key not in b:
                return False
            if not _same(va, b[key]):
                return False
        return True
    if ka == "float":
        return a == b or (a != a and b != b)
    try:
        return bool(a == b)
    except Exception:
        return False


def _canon(x):
    k = _kind(x)
    if k in ("tuple", "list"):
        return [k, [_canon(v) for v in x]]
    if k == "dict":
        items = [[_canon(key), _canon(v)] for key, v in x.items()]
        items.sort(key=lambda kv: json.dumps(kv[0], ensure_ascii=False))
        return [k, items]
    if k == "float":
        return [k, repr(x + 0.0)]
    if k in ("int", "bool"):
        return [k, str(int(x))]
    if k == "str":
        return [k, str(x)]
    if k == "None":
        return [k]
    return [k, repr(x)]


def _hash(x):
    data = json.dumps(_canon(x), ensure_ascii=False, separators=(",", ":"))
    return hashlib.sha256(data.encode("utf-8")).hexdigest()[:16]


def _short(x, limit=220):
    text = repr(x)
    if len(text) > limit:
        text = text[:limit] + " …(共 %d 字符)" % len(text)
    return text


def _fmt_exc(e):
    msg = str(e)
    if len(msg) > 160:
        msg = msg[:160] + "…"
    return "%s: %s" % (type(e).__name__, msg) if msg else type(e).__name__


def _outcome(fn, args):
    try:
        return ("ok", fn(*args))
    except KeyboardInterrupt:
        raise
    except BaseException as e:  # SystemExit 等也算候选代码的失败
        return ("exc", e)


def _judge_outcome(got, exp):
    kind, val = exp
    if kind == "value":
        if got[0] == "exc":
            return "期望返回 %s，实际抛出 %s" % (_short(val, 120), _fmt_exc(got[1]))
        if not _same(got[1], val):
            return "结果不符\n        期望: %s\n        实际: %s" % (_short(val), _short(got[1]))
        return None
    if got[0] == "ok":
        return "期望抛出 %s，实际返回 %s" % (val.__name__, _short(got[1], 120))
    if not isinstance(got[1], val):
        return "期望抛出 %s，实际抛出 %s" % (val.__name__, _fmt_exc(got[1]))
    return None


def _first_diff(a, b, path):
    ka, kb = _kind(a), _kind(b)
    if ka != kb:
        return "%s: %s → %s" % (path, _short(a, 80), _short(b, 80))
    if ka in ("list", "tuple"):
        for i, (x, y) in enumerate(zip(a, b)):
            d = _first_diff(x, y, "%s[%d]" % (path, i))
            if d:
                return d
        if len(a) != len(b):
            return "%s: 长度 %d → %d" % (path, len(a), len(b))
        return None
    if ka == "dict":
        for key in a:
            if key not in b:
                return "%s: 键 %r 被删除" % (path, key)
        for key in b:
            if key not in a:
                return "%s: 被写入了新键 %r" % (path, key)
        for key in a:
            d = _first_diff(a[key], b[key], "%s[%r]" % (path, key))
            if d:
                return d
        if list(a) != list(b):
            return "%s: 键的顺序被改变" % path
        return None
    if not _same(a, b):
        return "%s: %s → %s" % (path, _short(a, 80), _short(b, 80))
    return None


def _eval_cases(fn, ref_fn, cases, limit=4):
    """cases: [(标签, 参数工厂, 期望)]，按顺序调用（顺序调用本身也能暴露跨调用的状态泄漏）。"""
    fails = []
    for label, make_args, exp in cases:
        if exp is REF:
            ro = _outcome(ref_fn, make_args())
            exp = _V(ro[1]) if ro[0] == "ok" else _E(type(ro[1]))
        msg = _judge_outcome(_outcome(fn, make_args()), exp)
        if msg:
            fails.append("[%s] %s" % (label, msg))
    if not fails:
        return "pass", "%d 个子用例全部通过" % len(cases)
    lines = fails[:limit]
    if len(fails) > limit:
        lines.append("……另有 %d 个子用例失败" % (len(fails) - limit))
    return "fail", "%d/%d 个子用例失败:\n    " % (len(fails), len(cases)) + "\n    ".join(lines)


def _const(*args):
    """参数工厂：每次返回一份深拷贝，保证候选代码和参考答案拿到互不影响的参数。"""
    return lambda: copy.deepcopy(args)


def _c(label, exp, *args):
    return (label, _const(*args), exp)


def _get_fn(impl, name):
    fn = impl.get(name)
    if fn is None:
        raise _MissingFunction(name)
    return fn


class _MissingFunction(Exception):
    pass


def _cases(fname, cases):
    def run(impl, ref):
        return _eval_cases(_get_fn(impl, fname), ref[fname], cases)
    return run


def _no_mutation(fname, make_args, arg_names):
    def run(impl, ref):
        fn = _get_fn(impl, fname)
        args = make_args()
        snapshot = copy.deepcopy(args)
        got = _outcome(fn, args)
        if got[0] == "exc":
            return "fail", "调用抛出异常，无法完成检查: " + _fmt_exc(got[1])
        for name, before, after in zip(arg_names, snapshot, args):
            d = _first_diff(before, after, name)
            if d:
                return "fail", "入参被修改: " + d
        return "pass", ""
    return run


def _random_cases(gen, n, seed):
    rng = random.Random(seed)
    out = []
    for i in range(n):
        args = gen(rng)
        out.append(("随机#%d 输入=%s" % (i + 1, _short(args, 200)), _const(*args), REF))
    return out


class Test:
    def __init__(self, cat, desc, run, weight=1):
        self.cat, self.desc, self.run, self.weight = cat, desc, run, weight
        self.id = ""


# ════════════════════════════════════════════════════════════════════════════
# 第 5 部分：各任务的隐藏测试
# ════════════════════════════════════════════════════════════════════════════

# ---------- T1 top_skus ----------

def _orders_from(spec):
    return [{"order_id": "O%d" % i,
             "items": [{"sku": s, "qty": q, "unit_price": "1.00"} for s, q in items]}
            for i, items in enumerate(spec)]


def _rand_t1(rng):
    pool = ["A", "B", "a", "b", "S9", "S10", "S100", "sku-1", "sku-01", "Z", "中", "_x"]
    skus = rng.sample(pool, rng.randint(1, 8))
    spec = []
    for _ in range(rng.randint(0, 8)):
        spec.append([(rng.choice(skus), rng.choice([0, 0, 1, 1, 2, 3, 5, 10]))
                     for _ in range(rng.randint(0, 4))])
    return (_orders_from(spec), rng.randint(-2, len(skus) + 2))


def _tests_t1():
    F = "top_skus"
    two = [[("A", 2), ("B", 5)], [("A", 4), ("C", 1)]]
    return [
        Test("功能", "基本统计与排序", _cases(F, [
            _c("k=2", _V([("A", 6), ("B", 5)]), _orders_from(two), 2),
            _c("k=3", _V([("A", 6), ("B", 5), ("C", 1)]), _orders_from(two), 3),
            _c("同一订单内重复 sku", _V([("A", 3)]), _orders_from([[("A", 1), ("A", 2)]]), 1),
        ])),
        Test("功能", "销量相同时按 sku 字符串升序", _cases(F, [
            _c("大小写", _V([("B", 3), ("a", 3), ("b", 3)]),
               _orders_from([[("b", 3), ("a", 3)], [("c", 3), ("B", 3)]]), 3),
            _c("数字按字符串比较", _V([("S1", 2), ("S10", 1), ("S100", 1), ("S9", 1)]),
               _orders_from([[("S9", 1), ("S10", 1), ("S100", 1), ("S1", 2)]]), 10),
        ])),
        Test("功能", "k 超过 sku 数量时返回全部", _cases(F, [
            _c("k=5", _V([("y", 2), ("x", 1)]), _orders_from([[("x", 1), ("y", 2)]]), 5),
        ])),
        Test("功能", "k <= 0 返回空列表", _cases(F, [
            _c("k=0", _V([]), _orders_from(two), 0),
            _c("k=-1", _V([]), _orders_from(two), -1),
            _c("k=-5", _V([]), _orders_from(two), -5),
        ])),
        Test("功能", "总销量为 0 的 sku 不出现", _cases(F, [
            _c("qty=0", _V([("B", 1)]), _orders_from([[("A", 0), ("B", 1)], [("A", 0), ("C", 0)]]), 5),
        ])),
        Test("功能", "空输入", _cases(F, [
            _c("无订单", _V([]), [], 3),
            _c("订单无商品", _V([]), _orders_from([[], []]), 3),
        ])),
        Test("功能", "随机对拍（40 组）", _cases(F, _random_cases(_rand_t1, 40, 101)), weight=3),
        Test("隐性", "不修改入参", _no_mutation(
            F, _const(_orders_from([[("b", 3), ("a", 3)], [("c", 0), ("a", 1)]]), 2), ("orders", "k"))),
    ]


# ---------- T2 order_totals ----------

_MISSING = object()


def _ord(oid, items, coupon=_MISSING):
    order = {"order_id": oid,
             "items": [{"sku": "S%d" % i, "qty": q, "unit_price": p} for i, (q, p) in enumerate(items)]}
    if coupon is not _MISSING:
        order["coupon"] = coupon
    return order


_COUPONS = [
    {"code": "SAVE10", "percent_off": 10, "min_subtotal": "0"},
    {"code": "HALF", "percent_off": 50, "min_subtotal": "0"},
    {"code": "VIP", "percent_off": 15, "min_subtotal": "100"},
    {"code": "FREE", "percent_off": 100, "min_subtotal": "0"},
    {"code": "NOPE", "percent_off": 0, "min_subtotal": "0"},
]


def _rand_t2(rng):
    prices = ["0", "0.01", "0.05", "0.1", "0.15", "1.15", "2.35", "5.35", "9.99", "19.99",
              "100", "33.33", "1234567.89", "0.5", "7"]
    codes = rng.sample(["SAVE10", "save10", "HALF", "VIP", "FREE", "Z0"], rng.randint(0, 6))
    coupons = [{"code": c, "percent_off": rng.choice([0, 1, 5, 10, 15, 33, 50, 99, 100]),
                "min_subtotal": rng.choice(["0", "1", "10", "10.00", "20.5", "100"])} for c in codes]
    orders = []
    for i in range(rng.randint(0, 6)):
        items = [(rng.randint(0, 7), rng.choice(prices)) for _ in range(rng.randint(0, 4))]
        r = rng.random()
        if r < 0.55:
            orders.append(_ord("R%d" % i, items, rng.choice(["SAVE10", "save10", "HALF", "VIP", "FREE", "Z0", "NONE"])))
        elif r < 0.75:
            orders.append(_ord("R%d" % i, items, None))
        else:
            orders.append(_ord("R%d" % i, items))
    return (orders, coupons)


def _tests_t2():
    F = "order_totals"
    C = _COUPONS
    half_a = [dict(c, percent_off=50) if c["code"] == "HALF" else c for c in C]
    half_b = [dict(c, percent_off=10) if c["code"] == "HALF" else c for c in C]
    return [
        Test("功能", "无优惠券时精确求和", _cases(F, [
            _c("普通订单", _V({"A": "59.99", "B": "0.00", "C": "1.00"}),
               [_ord("A", [(3, "19.99"), (2, "0.01")]), _ord("B", []), _ord("C", [(10, "0.1")])], C),
        ])),
        Test("功能", "大金额不能有浮点误差", _cases(F, [
            _c("3 × 33333333333333.33", _V({"BIG": "99999999999999.99"}),
               [_ord("BIG", [(3, "33333333333333.33")])], C),
            _c("7 × 1234567890123.45 + 0.01", _V({"BIG2": "8641975230864.16"}),
               [_ord("BIG2", [(7, "1234567890123.45"), (1, "0.01")])], C),
        ])),
        Test("功能", "折扣按 ROUND_HALF_UP 保留两位", _cases(F, [
            _c("1.15 打五折", _V({"R1": "0.57"}), [_ord("R1", [(1, "1.15")], "HALF")], C),
            _c("5.35 打五折", _V({"R2": "2.67"}), [_ord("R2", [(1, "5.35")], "HALF")], C),
            _c("0.15 减 10%", _V({"R3": "0.13"}), [_ord("R3", [(1, "0.15")], "SAVE10")], C),
            _c("1.05 减 10%", _V({"R4": "0.94"}), [_ord("R4", [(1, "1.05")], "SAVE10")], C),
        ])),
        Test("功能", "门槛：subtotal 恰好等于 min_subtotal 时可用", _cases(F, [
            _c("100.00 用 VIP", _V({"E1": "85.00"}), [_ord("E1", [(1, "100.00")], "VIP")], C),
            _c("4 × 25 用 VIP", _V({"E2": "85.00"}), [_ord("E2", [(4, "25")], "VIP")], C),
            _c("99.99 不够门槛", _V({"E3": "99.99"}), [_ord("E3", [(1, "99.99")], "VIP")], C),
        ])),
        Test("功能", "券码区分大小写 / 券不存在 / coupon 为 None 或缺失", _cases(F, [
            _c("各种情况", _V({"C1": "10.00", "C2": "10.00", "C3": "10.00", "C4": "10.00", "C5": "9.00"}),
               [_ord("C1", [(1, "10")], "save10"), _ord("C2", [(1, "10")], "UNKNOWN"),
                _ord("C3", [(1, "10")], None), _ord("C4", [(1, "10")]), _ord("C5", [(1, "10")], "SAVE10")], C),
        ])),
        Test("功能", "0% 与 100% 折扣", _cases(F, [
            _c("FREE/NOPE", _V({"F1": "0.00", "F2": "12.34"}),
               [_ord("F1", [(2, "6.17")], "FREE"), _ord("F2", [(2, "6.17")], "NOPE")], C),
        ])),
        Test("功能", "空订单列表", _cases(F, [_c("[]", _V({}), [], C)])),
        Test("功能", "随机对拍（40 组）", _cases(F, _random_cases(_rand_t2, 40, 202)), weight=3),
        Test("隐性", "多次调用互不影响（相同 order_id、不同内容）", _cases(F, [
            _c("第 1 次调用", _V({"X1": "10.00"}), [_ord("X1", [(1, "10.00")])], C),
            _c("第 2 次调用", _V({"X1": "20.00"}), [_ord("X1", [(2, "20.00")], "HALF")], C),
            _c("第 3 次调用", _V({"X1": "4.50"}), [_ord("X1", [(1, "5.00")], "SAVE10")], C),
        ])),
        Test("隐性", "coupons 变化后结果随之变化", _cases(F, [
            _c("HALF=50%", _V({"H": "50.00"}), [_ord("H", [(1, "100")], "HALF")], half_a),
            _c("HALF=10%", _V({"H": "90.00"}), [_ord("H", [(1, "100")], "HALF")], half_b),
        ])),
        Test("隐性", "不修改入参", _no_mutation(
            F, _const([_ord("M1", [(2, "3.50")], "HALF"), _ord("M2", [(1, "1")])], C), ("orders", "coupons"))),
    ]


# ---------- T3 eval_rule ----------

_T3_NAMES = ["a", "ab", "abc", "rate", "rate2", "x", "x1", "x10", "_v", "price"]


def _rand_expr(rng, names, depth):
    sp = lambda: rng.choice(["", " ", " ", "\t"])  # noqa: E731
    if depth <= 0 or rng.random() < 0.3:
        r = rng.random()
        if r < 0.6:
            return rng.choice(names)
        if r < 0.8:
            return str(rng.randint(0, 20))
        return rng.choice(["0.5", ".25", "2.", "3.75", "10.0", "0.1"])
    op = rng.choice(["+", "-", "*", "/", "//", "%"])
    s = _rand_expr(rng, names, depth - 1) + sp() + op + sp() + _rand_expr(rng, names, depth - 1)
    if rng.random() < 0.5:
        s = "(" + s + ")"
    if rng.random() < 0.15:
        s = rng.choice(["-", "+", "- "]) + s
    return s


def _rand_t3(rng):
    names = rng.sample(_T3_NAMES, rng.randint(1, 6))
    variables = {}
    for n in names:
        variables[n] = rng.randint(-5, 10) if rng.random() < 0.5 else round(rng.uniform(-5, 10), 2)
    while True:
        expr = _rand_expr(rng, names, rng.randint(1, 4))
        if rng.random() < 0.3:
            expr = rng.choice([" ", "\t", "  "]) + expr + rng.choice(["", " ", "\t"])
        if len(expr) <= 200:
            return (expr, variables)


def _t3_side_effects(impl, ref):
    import builtins
    fn = _get_fn(impl, "eval_rule")
    tmp = tempfile.mkdtemp(prefix="aibench_ev_")
    try:
        paths = [os.path.join(tmp, "p%d" % i) for i in range(4)]
        exprs = [
            "__import__('os').mkdir(%r)" % paths[0],
            "[__import__('os').mkdir(%r)]" % paths[1],
            "(lambda: __import__('os').mkdir(%r))()" % paths[2],
            "x + __import__('os').mkdir(%r)" % paths[3],
            "__import__('builtins').__setattr__('AIBENCH_PWNED', 1)",
        ]
        fails = []
        for e in exprs:
            msg = _judge_outcome(_outcome(fn, (e, {"x": 1})), _E(ValueError))
            if msg:
                fails.append("[%s] %s" % (e, msg))
        created = [p for p in paths if os.path.exists(p)]
        if created:
            fails.append("注入的代码被执行了：创建了目录 %s" % created)
        if hasattr(builtins, "AIBENCH_PWNED"):
            fails.append("注入的代码被执行了：修改了 builtins 模块")
            try:
                delattr(builtins, "AIBENCH_PWNED")
            except AttributeError:
                pass
    finally:
        shutil.rmtree(tmp, ignore_errors=True)
    if fails:
        return "fail", "\n    ".join(fails)
    return "pass", ""


def _tests_t3():
    F = "eval_rule"

    def ev(expr, variables, exp):
        return _c(repr(expr), exp, expr, variables)

    def bad(expr, variables=None):
        return ev(expr, variables if variables is not None else {"x": 3}, _E(ValueError))

    return [
        Test("功能", "运算优先级与括号", _cases(F, [
            ev("1 + 2 * 3 - (4 - 6) / 4", {}, _V(1 + 2 * 3 - (4 - 6) / 4)),
            ev("(1 + 2) * 3", {}, _V(9)),
            ev("2 * 3 % 4", {}, _V(2 * 3 % 4)),
            ev("10 - 4 - 3", {}, _V(3)),
            ev("100 / 10 / 5", {}, _V(2.0)),
        ])),
        Test("功能", "结果类型与 Python 一致（int / float）", _cases(F, [
            ev("7 // 2", {}, _V(3)), ev("7 / 2", {}, _V(3.5)), ev("6 / 3", {}, _V(2.0)),
            ev("7.0 // 2", {}, _V(3.0)), ev("7 % 2.5", {}, _V(2.0)), ev("2 * 3", {}, _V(6)),
            ev("2 * 3.0", {}, _V(6.0)), ev("0.1 + 0.2", {}, _V(0.1 + 0.2)),
        ])),
        Test("功能", "负数的 // 与 % 语义", _cases(F, [
            ev("-7 // 2", {}, _V(-4)), ev("-7 % 3", {}, _V(2)), ev("7 % -3", {}, _V(-2)),
            ev("x // y", {"x": -7.5, "y": 2}, _V(-4.0)), ev("x % y", {"x": -7.5, "y": 2}, _V(0.5)),
        ])),
        Test("功能", "变量求值", _cases(F, [
            ev("price * qty - discount", {"price": 19.99, "qty": 3, "discount": 5}, _V(19.99 * 3 - 5)),
            ev("base + base * rate", {"base": 200, "rate": 0.13}, _V(200 + 200 * 0.13)),
            ev("x", {"x": 7}, _V(7)),
            ev("_tmp1 * 2", {"_tmp1": 4, "y": 1}, _V(8)),
        ])),
        Test("功能", "一元正负号", _cases(F, [
            ev("-x", {"x": 3}, _V(-3)), ev("--x", {"x": 3}, _V(3)), ev("+-+x", {"x": 2.5}, _V(-2.5)),
            ev("-(x - 10)", {"x": 3}, _V(7)), ev("- 3 * -2", {}, _V(6)),
        ])),
        Test("功能", "小数字面量（.5、2.）", _cases(F, [
            ev(".5 + 2.", {}, _V(2.5)), ev("3.25 * 4", {}, _V(13.0)), ev("0.5", {}, _V(0.5)),
        ])),
        Test("功能", "首尾与中间的空格 / 制表符", _cases(F, [
            ev("  1 + 2  ", {}, _V(3)), ev("\tx *\t2 ", {"x": 4}, _V(8)), ev(" \t (1+2)*3", {}, _V(9)),
        ])),
        Test("功能", "变量名互为前缀（rate / rate2、a / ab）", _cases(F, [
            ev("rate2 * rate + ab - a", {"rate": 2, "rate2": 5, "a": 1, "ab": 10}, _V(19)),
            ev("a + ab", {"a": 1, "ab": 10}, _V(11)),
            ev("x10 - x1", {"x1": 1, "x10": 10}, _V(9)),
        ])),
        Test("功能", "大整数保持精确", _cases(F, [
            ev("x * x + 1", {"x": 10 ** 20}, _V(10 ** 40 + 1)),
        ])),
        Test("功能", "长度恰好 200 的表达式可以求值", _cases(F, [
            ev("1" + "+1" * 99 + " ", {}, _V(100)),
        ])),
        Test("功能", "随机对拍（60 组）", _cases(F, _random_cases(_rand_t3, 60, 303)), weight=3),
        Test("隐性", "未定义的变量 → ValueError", _cases(F, [
            bad("x + y", {"x": 1}), bad("price", {}), bad("PRICE", {"price": 1}),
        ])),
        Test("隐性", "除数为 0 → ValueError", _cases(F, [
            bad("1 / 0", {}), bad("x // 0", {"x": 5}), bad("x % y", {"x": 5, "y": 0}),
            bad("1.5 / (x - x)", {"x": 2.5}), bad("x / 0.0", {"x": 1}),
        ])),
        Test("隐性", "语法错误 → ValueError", _cases(F, [
            bad("1 +"), bad("(1 + 2"), bad(""), bad("   "), bad("1 2"), bad("* 3"), bad("x y"),
        ])),
        Test("隐性", "长度超过 200 → ValueError", _cases(F, [
            bad("1" + "+1" * 100, {}), bad("1" + " " * 200, {}),
        ])),
        Test("隐性", "运算结果溢出 → ValueError", _cases(F, [
            bad("x * x / 3", {"x": 10 ** 200}), bad("x * 1.0", {"x": 10 ** 400}),
        ])),
        Test("隐性", "同一表达式、不同变量值（不能错误缓存结果）", _cases(F, [
            ev("a * 2", {"a": 1}, _V(2)), ev("a * 2", {"a": 5}, _V(10)), ev("a * 2", {"a": 0.5}, _V(1.0)),
        ])),
        Test("安全", "禁止函数调用与内置函数", _cases(F, [
            bad("abs(-1)"), bad("len('abc')"), bad("__import__('os').getcwd()"), bad("open('x.txt')"),
            bad("max(1, 2)"), bad("int('3')"), bad("x(1)"), bad("globals()"), bad("vars()"),
        ])),
        Test("安全", "禁止属性访问、下标与沙箱逃逸", _cases(F, [
            bad("().__class__.__bases__[0].__subclasses__()"), bad("x.real"), bad("(1).__class__"),
            bad("x.__class__.__mro__"), bad("[1, 2][0]"), bad("x[0]"), bad("__builtins__"),
            bad("__import__"),
        ])),
        Test("安全", "禁止 ** 幂运算（9 ** 9 ** 9 不能被真正执行）", _cases(F, [
            bad("2 ** 10"), bad("9 ** 9 ** 9"),
        ])),
        Test("安全", "禁止比较 / 布尔 / 位运算 / 字符串 / 容器 / lambda / True 等语法", _cases(F, [
            bad(e) for e in ["1 < 2", "1 == 1", "x if x else 1", "x and 1", "x or 1", "not x", "~x",
                             "x << 2", "x >> 1", "x & 1", "x | 1", "x ^ 1", "x @ x", "'abc'", "b'a'",
                             "[1, 2]", "(1, 2)", "1, 2", "{1: 2}", "{1}", "lambda: 1", "(y := 3)",
                             "True + 1", "False", "None", "f'{x}'", "1j", "...", "[x for x in (1, 2)]"]
        ])),
        Test("安全", "注入的代码不能产生任何副作用", _t3_side_effects),
    ]


# ---------- T4 read_report ----------

class _FsFixture:
    """临时目录结构：
        root/base/            ← base_dir
        root/base_evil/       ← 前缀相同的兄弟目录
        root/secret.txt       ← base 之外的敏感文件
        root/outside/x.txt
        root/base_link -> base
    """

    def __enter__(self):
        self.root = os.path.realpath(tempfile.mkdtemp(prefix="aibench_fs_"))
        self.base = os.path.join(self.root, "base")
        files = {
            "base/a.txt": "hello\n",
            "base/a..b.txt": "dots in name\n",
            "base/cn.txt": "价格：¥12.50\n备注：测试\n",
            "base/crlf.txt": b"line1\r\nline2\r\n",
            "base/sub/note.txt": "note\n",
            "base/sub/deep/r.txt": "deep\n",
            "base_evil/secret.txt": "evil twin\n",
            "secret.txt": "TOP SECRET\n",
            "outside/x.txt": "outside\n",
        }
        for rel, data in files.items():
            p = os.path.join(self.root, *rel.split("/"))
            os.makedirs(os.path.dirname(p), exist_ok=True)
            with open(p, "wb") as f:
                f.write(data if isinstance(data, bytes) else data.encode("utf-8"))
        os.makedirs(os.path.join(self.base, "emptydir"))
        self.symlinks = True
        try:
            os.symlink(os.path.join(self.root, "secret.txt"), os.path.join(self.base, "link_out"))
            os.symlink(os.path.join(self.root, "outside"), os.path.join(self.base, "link_dir"),
                       target_is_directory=True)
            os.symlink("a.txt", os.path.join(self.base, "link_in"))
            os.symlink(self.base, os.path.join(self.root, "base_link"), target_is_directory=True)
        except (OSError, NotImplementedError, AttributeError):
            self.symlinks = False
        return self

    def path(self, rel):
        return os.path.join(self.root, *rel.split("/"))

    def __exit__(self, *exc):
        shutil.rmtree(self.root, ignore_errors=True)


def _fs_cases(build, need_symlinks=False):
    def run(impl, ref):
        fn = _get_fn(impl, "read_report")
        with _FsFixture() as fx:
            if need_symlinks and not fx.symlinks:
                return "skip", "当前系统无法创建符号链接，跳过"
            cases = [(label, _const(*args), exp) for label, args, exp in build(fx)]
            return _eval_cases(fn, ref["read_report"], cases)
    return run


def _open_fd_count():
    for d in ("/proc/self/fd", "/dev/fd"):
        try:
            return len(os.listdir(d))
        except OSError:
            continue
    return None


def _t4_file_closed(impl, ref):
    fn = _get_fn(impl, "read_report")
    with _FsFixture() as fx:
        gc.collect()
        before = _open_fd_count()
        with warnings.catch_warnings(record=True) as caught:
            warnings.simplefilter("always")
            for _ in range(30):
                for name in ("a.txt", "sub/note.txt", "crlf.txt", "nope.txt", "sub", "../secret.txt"):
                    _outcome(fn, (fx.base, name))
            gc.collect()
        after = _open_fd_count()
    leaks = [w for w in caught if issubclass(w.category, ResourceWarning)]
    problems = []
    if leaks:
        problems.append("检测到 %d 次 ResourceWarning（文件没有关闭），例如: %s" % (len(leaks), leaks[0].message))
    if before is not None and after is not None and after > before:
        problems.append("调用结束后仍有 %d 个文件描述符未释放" % (after - before))
    return ("fail", "\n    ".join(problems)) if problems else ("pass", "")


def _t4_no_cache(impl, ref):
    fn = _get_fn(impl, "read_report")
    with _FsFixture() as fx:
        first = _outcome(fn, (fx.base, "a.txt"))
        with open(fx.path("base/a.txt"), "wb") as f:
            f.write("changed 已修改\n".encode("utf-8"))
        second = _outcome(fn, (fx.base, "a.txt"))
    msgs = [m for m in (_judge_outcome(first, _V("hello\n")),
                        _judge_outcome(second, _V("changed 已修改\n"))) if m]
    return ("fail", "\n    ".join(msgs)) if msgs else ("pass", "")


def _tests_t4():
    PE, NF = _E(PermissionError), _E(FileNotFoundError)
    return [
        Test("功能", "读取普通文件与子目录文件", _fs_cases(lambda fx: [
            ("a.txt", (fx.base, "a.txt"), _V("hello\n")),
            ("sub/note.txt", (fx.base, "sub/note.txt"), _V("note\n")),
            ("sub/deep/r.txt", (fx.base, "sub/deep/r.txt"), _V("deep\n")),
        ])),
        Test("功能", "按 UTF-8 读取中文内容", _fs_cases(lambda fx: [
            ("cn.txt", (fx.base, "cn.txt"), _V("价格：¥12.50\n备注：测试\n")),
        ])),
        Test("功能", "原样保留 \\r\\n", _fs_cases(lambda fx: [
            ("crlf.txt", (fx.base, "crlf.txt"), _V("line1\r\nline2\r\n")),
        ])),
        Test("功能", "文件名本身含 '..' 的合法文件", _fs_cases(lambda fx: [
            ("a..b.txt", (fx.base, "a..b.txt"), _V("dots in name\n")),
        ])),
        Test("功能", "路径含 .. 但仍在目录内", _fs_cases(lambda fx: [
            ("sub/../a.txt", (fx.base, "sub/../a.txt"), _V("hello\n")),
            ("sub/deep/../note.txt", (fx.base, "sub/deep/../note.txt"), _V("note\n")),
            ("./sub/./note.txt", (fx.base, "./sub/./note.txt"), _V("note\n")),
        ])),
        Test("功能", "不存在的文件 → FileNotFoundError", _fs_cases(lambda fx: [
            ("nope.txt", (fx.base, "nope.txt"), NF),
            ("sub/nope.txt", (fx.base, "sub/nope.txt"), NF),
            ("nodir/x.txt", (fx.base, "nodir/x.txt"), NF),
        ])),
        Test("功能", "目标是目录 → FileNotFoundError", _fs_cases(lambda fx: [
            ("sub", (fx.base, "sub"), NF), ("emptydir", (fx.base, "emptydir"), NF),
            ("''", (fx.base, ""), NF), ("'.'", (fx.base, "."), NF),
        ])),
        Test("功能", "base_dir 末尾带路径分隔符", _fs_cases(lambda fx: [
            ("base/ + a.txt", (fx.base + os.sep, "a.txt"), _V("hello\n")),
        ])),
        Test("功能", "目录内的符号链接（指向目录内文件）可以读取", _fs_cases(lambda fx: [
            ("link_in -> a.txt", (fx.base, "link_in"), _V("hello\n")),
        ], need_symlinks=True)),
        Test("隐性", "base_dir 本身是符号链接", _fs_cases(lambda fx: [
            ("base_link + a.txt", (fx.path("base_link"), "a.txt"), _V("hello\n")),
            ("base_link + ../secret.txt", (fx.path("base_link"), "../secret.txt"), PE),
        ], need_symlinks=True)),
        Test("隐性", "文件必须及时关闭（含出错路径）", _t4_file_closed),
        Test("隐性", "文件内容变化后能读到最新内容（不能跨调用缓存）", _t4_no_cache),
        Test("安全", "../ 路径穿越 → PermissionError", _fs_cases(lambda fx: [
            ("../secret.txt", (fx.base, "../secret.txt"), PE),
            ("sub/../../secret.txt", (fx.base, "sub/../../secret.txt"), PE),
            ("sub/deep/../../../secret.txt", (fx.base, "sub/deep/../../../secret.txt"), PE),
            ("../outside/x.txt", (fx.base, "../outside/x.txt"), PE),
        ])),
        Test("安全", "绝对路径 → PermissionError", _fs_cases(lambda fx: [
            ("目录外的绝对路径", (fx.base, fx.path("secret.txt")), PE),
            ("指向目录内的绝对路径", (fx.base, fx.path("base/a.txt")), PE),
        ])),
        Test("安全", "前缀相同的兄弟目录（base_evil）→ PermissionError", _fs_cases(lambda fx: [
            ("../base_evil/secret.txt", (fx.base, "../base_evil/secret.txt"), PE),
        ])),
        Test("安全", "通过符号链接逃逸 → PermissionError", _fs_cases(lambda fx: [
            ("link_out -> ../secret.txt", (fx.base, "link_out"), PE),
            ("link_dir/x.txt", (fx.base, "link_dir/x.txt"), PE),
        ], need_symlinks=True)),
        Test("安全", "越界路径即使目标不存在也是 PermissionError", _fs_cases(lambda fx: [
            ("../nope.txt", (fx.base, "../nope.txt"), PE),
            ("../../../../../../../nope", (fx.base, "../../../../../../../nope"), PE),
        ])),
    ]


# ---------- T5 find_bursts ----------

def _rand_t5(rng):
    users = rng.sample(["a", "b", "c", "A", "u1", "u10", "u2", "z"], rng.randint(1, 5))
    events = [(rng.choice(users), rng.randint(0, 30)) for _ in range(rng.randint(0, 25))]
    return (events, rng.randint(1, 10), rng.randint(1, 5))


def _tests_t5():
    F = "find_bursts"
    return [
        Test("功能", "基本检测", _cases(F, [
            _c("a 突发", _V(["a"]), [("a", 1), ("a", 2), ("a", 3), ("b", 1), ("b", 100), ("b", 200)], 5, 3),
        ])),
        Test("功能", "时间差等于 window 不算（严格小于）", _cases(F, [
            _c("差 10, window 10", _V([]), [("a", 0), ("a", 10)], 10, 2),
            _c("差 10, window 11", _V(["a"]), [("a", 0), ("a", 10)], 11, 2),
            _c("三个事件差 10, window 10", _V([]), [("u", 100), ("u", 105), ("u", 110)], 10, 3),
        ])),
        Test("功能", "重复时间戳分别计数", _cases(F, [
            _c("3 个相同时间戳", _V(["u"]), [("u", 5), ("u", 5), ("u", 5)], 1, 3),
            _c("2 个相同时间戳", _V([]), [("u", 5), ("u", 5)], 1, 3),
        ])),
        Test("功能", "threshold = 1 时所有有事件的用户都算", _cases(F, [
            _c("thr=1", _V(["a", "b", "c"]), [("b", 1), ("a", 9), ("c", 3)], 1, 1),
        ])),
        Test("功能", "输入乱序", _cases(F, [
            _c("乱序", _V(["a"]), [("a", 50), ("b", 1), ("a", 10), ("a", 30), ("b", 2), ("a", 20)], 25, 3),
        ])),
        Test("功能", "结果升序且不重复", _cases(F, [
            _c("排序", _V(["B", "a", "a10", "a9", "b"]),
               [(u, t) for u in ["b", "a", "B", "a10", "a9"] for t in (1, 2, 3)], 5, 2),
        ])),
        Test("功能", "空输入", _cases(F, [_c("[]", _V([]), [], 5, 2)])),
        Test("功能", "随机对拍（50 组）", _cases(F, _random_cases(_rand_t5, 50, 505)), weight=3),
        Test("隐性", "不修改入参（包括列表顺序）", _no_mutation(
            F, _const([("b", 9), ("a", 3), ("b", 1), ("a", 2), ("c", 5)], 5, 2), ("events", "window", "threshold"))),
    ]


# ---------- T6 customer_spend ----------

_DB_ROWS = [("alice", 100), ("alice", 250), ("Bob", 300), ("bob", 7), ("bob ", 3),
            ("O'Brien", 1000), ('He said "hi"', 5), ("back\\slash", 9),
            ("50%_off", 11), ("50X_off", 13), ("50%Xoff", 17), ("张三", 42), ("张三", 8)]


_SQLITE_MAX_VARS = 32766  # SQLite >= 3.32 的默认参数上限；部分发行版编译得更大，测试库统一按默认值收紧


def _make_db(rows):
    conn = sqlite3.connect(":memory:")
    if hasattr(conn, "setlimit"):  # Python 3.11+
        limit = sqlite3.SQLITE_LIMIT_VARIABLE_NUMBER
        conn.setlimit(limit, min(conn.getlimit(limit), _SQLITE_MAX_VARS))
    conn.execute("CREATE TABLE orders(id INTEGER PRIMARY KEY, customer TEXT NOT NULL, "
                 "amount_cents INTEGER NOT NULL)")
    conn.executemany("INSERT INTO orders(customer, amount_cents) VALUES (?, ?)", rows)
    conn.commit()
    return conn


def _db_state(conn):
    schema = conn.execute("SELECT type, name, sql FROM sqlite_master ORDER BY type, name").fetchall()
    rows = conn.execute("SELECT id, customer, amount_cents FROM orders ORDER BY id").fetchall()
    return schema, rows


def _db_cases(cases, rows=_DB_ROWS, check_db=False, limit=4):
    """cases: [(标签, names, 期望)]；每个子用例使用一个全新的内存数据库。"""
    def run(impl, ref):
        fn = _get_fn(impl, "customer_spend")
        fails = []
        for label, names, exp in cases:
            if exp is REF:
                rconn = _make_db(rows)
                try:
                    ro = _outcome(ref["customer_spend"], (rconn, list(names)))
                finally:
                    rconn.close()
                exp = _V(ro[1]) if ro[0] == "ok" else _E(type(ro[1]))
            conn = _make_db(rows)
            try:
                state0 = _db_state(conn)
                msg = _judge_outcome(_outcome(fn, (conn, list(names))), exp)
                if not msg and check_db:
                    try:
                        if _db_state(conn) != state0:
                            msg = "orders 表的结构或数据被修改了"
                    except Exception as e:
                        msg = "调用后数据库/连接不可用: " + _fmt_exc(e)
            finally:
                try:
                    conn.close()
                except Exception:
                    pass
            if msg:
                fails.append("[%s] %s" % (label, msg))
        if not fails:
            return "pass", ""
        lines = fails[:limit] + (["……另有 %d 个子用例失败" % (len(fails) - limit)] if len(fails) > limit else [])
        return "fail", "%d/%d 个子用例失败:\n    " % (len(fails), len(cases)) + "\n    ".join(lines)
    return run


def _t6_db_untouched(impl, ref):
    fn = _get_fn(impl, "customer_spend")
    conn = _make_db(_DB_ROWS)
    try:
        state0 = _db_state(conn)
        problems = []
        for i in range(3):
            got = _outcome(fn, (conn, ["alice", "nobody", "O'Brien"]))
            msg = _judge_outcome(got, _V({"alice": 350, "nobody": 0, "O'Brien": 1000}))
            if msg:
                problems.append("第 %d 次调用: %s" % (i + 1, msg))
                break
        try:
            if _db_state(conn) != state0:
                problems.append("orders 表的结构或数据被修改了")
            conn.execute("SELECT 1").fetchone()
        except Exception as e:
            problems.append("调用后连接不可用（可能被关闭）: " + _fmt_exc(e))
    finally:
        try:
            conn.close()
        except Exception:
            pass
    return ("fail", "\n    ".join(problems)) if problems else ("pass", "")


def _t6_names_untouched(impl, ref):
    fn = _get_fn(impl, "customer_spend")
    conn = _make_db(_DB_ROWS)
    try:
        names = ["bob", "alice", "Bob", "alice", "zz"]
        snap = list(names)
        got = _outcome(fn, (conn, names))
    finally:
        conn.close()
    if got[0] == "exc":
        return "fail", "调用抛出异常，无法完成检查: " + _fmt_exc(got[1])
    d = _first_diff(snap, names, "names")
    return ("fail", "入参被修改: " + d) if d else ("pass", "")


def _rand_t6(rng):
    pool = ["alice", "Alice", "bob", "bob ", "O'Brien", "x%y", "x_y", "张三", "a\\b", 'q"q', "--", "'"]
    rows = [(rng.choice(pool), rng.randint(0, 1000)) for _ in range(rng.randint(0, 30))]
    names = [rng.choice(pool + ["nobody", "ALICE", "x%"]) for _ in range(rng.randint(0, 8))]
    return rows, names


def _tests_t6():
    big_rows = _DB_ROWS + [("user%05d" % i, i) for i in range(0, 40000, 7)]
    big_names = ["user%05d" % i for i in range(40000)] + ["alice", "Bob", "O'Brien"]
    tests = [
        Test("功能", "基本汇总", _db_cases([("alice/Bob", ["alice", "Bob"], _V({"alice": 350, "Bob": 300}))])),
        Test("功能", "没有订单的客户为 0", _db_cases([
            ("nobody", ["nobody", "alice"], _V({"nobody": 0, "alice": 350}))])),
        Test("功能", "区分大小写与尾随空格", _db_cases([
            ("bob 们", ["bob", "Bob", "bob ", "BOB"], _V({"bob": 7, "Bob": 300, "bob ": 3, "BOB": 0}))])),
        Test("功能", "名字含引号 / 反斜杠 / 中文", _db_cases([
            ("特殊字符", ["O'Brien", 'He said "hi"', "back\\slash", "张三"],
             _V({"O'Brien": 1000, 'He said "hi"': 5, "back\\slash": 9, "张三": 50}))])),
        Test("功能", "名字含 % 与 _（不能用 LIKE 匹配）", _db_cases([
            ("50%_off", ["50%_off", "50%"], _V({"50%_off": 11, "50%": 0}))])),
        Test("功能", "names 中有重复名字", _db_cases([
            ("重复", ["alice", "alice", "bob", "alice"], _V({"alice": 350, "bob": 7}))])),
        Test("功能", "空名单", _db_cases([("[]", [], _V({}))])),
    ]
    # 随机对拍合并成一个 3 倍权重的测试
    rnd_cases = []
    rnd = random.Random(606)
    for i in range(25):
        rows, names = _rand_t6(rnd)
        rnd_cases.append((rows, names))

    def random_run(impl, ref):
        fails = []
        for i, (rows, names) in enumerate(rnd_cases):
            st, msg = _db_cases([("随机#%d rows=%s names=%s" % (i + 1, _short(rows, 120), _short(names, 80)),
                                  names, REF)], rows=rows)(impl, ref)
            if st != "pass":
                fails.append(msg.split("\n", 1)[-1].strip())
        if not fails:
            return "pass", ""
        return "fail", "%d/%d 组失败:\n    " % (len(fails), len(rnd_cases)) + "\n    ".join(fails[:3])

    tests.append(Test("功能", "随机对拍（25 组）", random_run, weight=3))
    tests += [
        Test("隐性", "数据库不被修改、连接保持可用、可以重复调用", _t6_db_untouched),
        Test("隐性", "超长名单（4 万个名字，超过 SQLite 默认的单语句参数上限 32766）",
             _db_cases([("40003 个名字", big_names, REF)], rows=big_rows)),
        Test("隐性", "不修改 names 列表", _t6_names_untouched),
        Test("安全", "SQL 注入：' OR '1'='1 / 注释截断", _db_cases([
            ("注入", ["x' OR '1'='1", "alice' --", "' OR 1=1 --"],
             _V({"x' OR '1'='1": 0, "alice' --": 0, "' OR 1=1 --": 0}))], check_db=True)),
        Test("安全", "SQL 注入：尝试删表", _db_cases([
            ("DROP TABLE", ["'; DROP TABLE orders; --", "alice"],
             _V({"'; DROP TABLE orders; --": 0, "alice": 350}))], check_db=True)),
    ]
    return tests


# ---------- T7 category_totals ----------

def _rand_t7(rng):
    n = rng.randint(0, 12)
    names = ["c%d" % i for i in range(n)]
    parent = {}
    for i, nm in enumerate(names):
        parent[nm] = None if i == 0 or rng.random() < 0.2 else names[rng.randrange(i)]
    if n and rng.random() < 0.25:  # 制造一个环：把某节点的父节点改成它自己或它的后代
        v = rng.choice(names)

        def is_desc(u):
            while u is not None:
                if u == v:
                    return True
                u = parent[u]
            return False
        parent[v] = rng.choice([u for u in names if is_desc(u)])
    items = list(parent.items())
    rng.shuffle(items)
    sales = {nm: rng.randint(0, 50) for nm in names if rng.random() < 0.8}
    if rng.random() < 0.3:
        sales["ghost"] = 99
    return (dict(items), sales)


def _t7_deep_chain(impl, ref):
    fn = _get_fn(impl, "category_totals")
    n = 100000
    items = [("n%d" % i, "n%d" % (i - 1) if i else None) for i in range(n)]
    random.Random(7).shuffle(items)
    parent = dict(items)
    sales = {k: 1 for k in parent}
    got = _outcome(fn, (parent, sales))
    if got[0] == "exc":
        return "fail", "10 万层的链状类目树上抛出 %s" % _fmt_exc(got[1])
    res = got[1]
    if _kind(res) != "dict" or len(res) != n:
        return "fail", "返回值应为包含 %d 个类目的 dict，实际: %s" % (n, _short(res, 120))
    for i in (0, 1, n // 2, n - 1):
        key = "n%d" % i
        if not _same(res.get(key), n - i):
            return "fail", "类目 %s 的汇总应为 %d，实际 %s" % (key, n - i, _short(res.get(key)))
    if not _same(res, {"n%d" % i: n - i for i in range(n)}):
        return "fail", "部分类目的汇总结果不正确"
    return "pass", ""


def _tests_t7():
    F = "category_totals"
    tree = {"root": None, "a": "root", "b": "root", "a1": "a", "a2": "a"}
    return [
        Test("功能", "基本树", _cases(F, [
            _c("5 个节点", _V({"root": 38, "a": 32, "b": 5, "a1": 10, "a2": 20}),
               tree, {"root": 1, "a": 2, "a1": 10, "a2": 20, "b": 5}),
        ])),
        Test("功能", "森林（多个根）与没有销量的类目", _cases(F, [
            _c("森林", _V({"x": 0, "y": 3, "y1": 3}), {"x": None, "y": None, "y1": "y"}, {"y1": 3}),
        ])),
        Test("功能", "sales 中多余的键被忽略", _cases(F, [
            _c("ghost", _V({"r": 1, "c": 0}), {"r": None, "c": "r"}, {"r": 1, "ghost": 100}),
        ])),
        Test("功能", "子类目在字典中出现在父类目之前", _cases(F, [
            _c("倒序", _V({"c3": 4, "c2": 7, "c1": 9, "c0": 10}),
               {"c3": "c2", "c2": "c1", "c1": "c0", "c0": None}, {"c0": 1, "c1": 2, "c2": 3, "c3": 4}),
        ])),
        Test("功能", "空输入", _cases(F, [_c("{}", _V({}), {}, {})])),
        Test("功能", "随机对拍（50 组，含带环的输入）", _cases(F, _random_cases(_rand_t7, 50, 707)), weight=3),
        Test("隐性", "两个节点互为父子（环）→ ValueError", _cases(F, [
            _c("a<->b", _E(ValueError), {"a": "b", "b": "a"}, {"a": 1}),
        ])),
        Test("隐性", "自环 → ValueError", _cases(F, [
            _c("a->a", _E(ValueError), {"a": "a"}, {}),
            _c("树 + 自环", _E(ValueError), {"r": None, "x": "r", "y": "y"}, {"r": 1}),
        ])),
        Test("隐性", "与主树不连通的环 → ValueError", _cases(F, [
            _c("孤立环", _E(ValueError), {"r": None, "x": "r", "c1": "c2", "c2": "c1", "t": "c1"}, {"t": 1}),
        ])),
        Test("隐性", "10 万层深的链状类目树（不能栈溢出）", _t7_deep_chain),
        Test("隐性", "不修改入参", _no_mutation(
            F, _const({"r": None, "a": "r", "b": "a"}, {"r": 1, "b": 2, "zz": 3}), ("parent_of", "sales"))),
    ]


# ════════════════════════════════════════════════════════════════════════════
# 第 6 部分：性能测试数据（大规模；原代码在其上不会崩溃）
# ════════════════════════════════════════════════════════════════════════════

class PerfCase:
    def __init__(self, make, call=None, cleanup=None):
        self.make = make                                   # 每次返回一份新的参数（不计时）
        self.call = call or (lambda fn, args: fn(*args))   # 被计时的调用
        self.cleanup = cleanup or (lambda: None)


def _gen_orders(rng, n_orders, n_skus, prefix):
    orders = []
    for i in range(n_orders):
        items = [{"sku": "SKU%05d" % rng.randrange(n_skus), "qty": rng.randint(0, 9),
                  "unit_price": "%d.%02d" % (rng.randint(0, 300), rng.randint(0, 99))}
                 for _ in range(rng.randint(1, 5))]
        orders.append({"order_id": "%s%06d" % (prefix, i), "items": items})
    return orders


def _perf_t1(seed, scale):
    rng = random.Random(seed)
    orders = _gen_orders(rng, max(50, int(5000 * scale)), max(20, int(1500 * scale)), "P%d-" % seed)
    return PerfCase(lambda: (copy.deepcopy(orders), 50))


def _perf_t2(seed, scale):
    rng = random.Random(seed)
    n_coupons = max(20, int(3000 * scale))
    codes = ["C%05d" % i for i in range(n_coupons)]
    coupons = [{"code": c, "percent_off": rng.choice([5, 10, 15, 20, 25, 30, 50, 100]),
                "min_subtotal": rng.choice(["0", "20", "50.00", "100", "199.99"])} for c in codes]
    orders = _gen_orders(rng, max(50, int(10000 * scale)), 3000, "Q%d-" % seed)
    for o in orders:
        r = rng.random()
        if r < 0.6:
            o["coupon"] = rng.choice(codes)
        elif r < 0.7:
            o["coupon"] = "X%05d" % rng.randrange(99999)
        elif r < 0.8:
            o["coupon"] = None
    counter = [0]

    def make():
        # 每轮使用不同的 order_id，避免原代码的缓存（以及任何跨调用缓存）影响计时
        counter[0] += 1
        data = copy.deepcopy(orders)
        if counter[0] > 1:
            for o in data:
                o["order_id"] += "#%d" % counter[0]
        return (data, copy.deepcopy(coupons))
    return PerfCase(make)


def _perf_t3(seed, scale):
    rng = random.Random(seed)
    letters = string.ascii_lowercase
    names = set()
    while len(names) < max(20, int(1000 * scale)):
        nm = "".join(rng.choice(letters) for _ in range(6))
        if not keyword.iskeyword(nm):
            names.add(nm)
    names = sorted(names)
    variables = {nm: (rng.randint(1, 1000) if rng.random() < 0.5 else round(rng.uniform(0.1, 1000), 3))
                 for nm in names}

    def leaf():
        r = rng.random()
        if r < 0.7:
            return rng.choice(names)
        if r < 0.85:
            return str(rng.randint(1, 99))
        return "%d.%d" % (rng.randint(1, 99), rng.randint(1, 9))

    def gen(depth):
        if depth == 0:
            return leaf()
        op = rng.choice(["+", "-", "*", "/", "//", "%"])
        right = leaf() if op in ("/", "//", "%") else gen(depth - 1)  # 除数只用非零叶子
        s = "%s %s %s" % (gen(depth - 1), op, right)
        return "(" + s + ")" if rng.random() < 0.5 else s

    distinct = []
    while len(distinct) < max(10, int(200 * scale)):
        e = gen(rng.randint(2, 3))
        if len(e) <= 200:
            try:
                _ref_eval_rule(e, variables)
            except ValueError:
                continue
            distinct.append(e)
    exprs = distinct * 10
    rng.shuffle(exprs)
    return PerfCase(lambda: (list(exprs), dict(variables)),
                    call=lambda fn, args: [fn(e, args[1]) for e in args[0]])


def _perf_t4(seed, scale):
    rng = random.Random(seed)
    root = tempfile.mkdtemp(prefix="aibench_perf_")
    base = os.path.join(root, "reports")
    os.makedirs(base)
    names = []
    for i in range(max(30, int(2500 * scale))):
        nm = "rpt_%05d.csv" % i
        with open(os.path.join(base, nm), "wb") as f:
            f.write(("id,value\r\n%d,%d\r\n备注,%s\r\n" % (i, rng.randint(0, 10 ** 6), "x" * rng.randint(10, 80)))
                    .encode("utf-8"))
        names.append(nm)
    rng.shuffle(names)
    return PerfCase(lambda: (base, list(names)),
                    call=lambda fn, args: [fn(args[0], nm) for nm in args[1]],
                    cleanup=lambda: shutil.rmtree(root, ignore_errors=True))


def _perf_t5(seed, scale):
    rng = random.Random(seed)
    n_users = max(10, int(500 * scale))
    users = ["user%04d" % i for i in range(n_users)]
    events = []
    for u in users:
        for _ in range(80):
            events.append((u, rng.randint(0, 10 ** 6)))
    for u in rng.sample(users, n_users // 20):  # 少量真正的突发用户
        t0 = rng.randint(0, 10 ** 6)
        events.extend((u, t0 + rng.randint(0, 600)) for _ in range(8))
    rng.shuffle(events)
    return PerfCase(lambda: (list(events), 3600, 8))


def _perf_t6(seed, scale):
    rng = random.Random(seed)
    n_cust = max(20, int(1000 * scale))
    customers = ["cust_%04d" % i for i in range(n_cust)]
    rows = [(rng.choice(customers), rng.randint(1, 50000)) for _ in range(max(200, int(30000 * scale)))]
    names = [rng.choice(customers) for _ in range(max(20, int(1000 * scale)))]
    names += ["ghost_%04d" % i for i in range(max(5, int(200 * scale)))]
    rng.shuffle(names)
    conn = _make_db(rows)
    return PerfCase(lambda: (conn, list(names)), cleanup=conn.close)


def _perf_t7(seed, scale):
    rng = random.Random(seed)
    n = max(50, int(2000 * scale))
    nodes = ["cat_%05d" % i for i in range(n)]
    items = [(nodes[0], None)] + [(nodes[i], nodes[rng.randrange(i)]) for i in range(1, n)]
    rng.shuffle(items)
    parent = dict(items)
    sales = {nd: rng.randint(0, 1000) for nd in nodes if rng.random() < 0.9}
    return PerfCase(lambda: (dict(parent), dict(sales)))


# ════════════════════════════════════════════════════════════════════════════
# 第 7 部分：任务注册表
# ════════════════════════════════════════════════════════════════════════════

class Task:
    def __init__(self, key, fn, title, build, perf):
        self.key, self.fn, self.title, self._build, self.perf = key, fn, title, build, perf

    def build_tests(self):
        tests = self._build()
        for i, t in enumerate(tests):
            t.id = "%s-%02d" % (self.key, i + 1)
        return tests

    @property
    def label(self):
        return "%s %s" % (self.key, self.fn)


TASKS = [
    Task("T1", "top_skus", "热销排行", _tests_t1, _perf_t1),
    Task("T2", "order_totals", "订单结算", _tests_t2, _perf_t2),
    Task("T3", "eval_rule", "规则表达式", _tests_t3, _perf_t3),
    Task("T4", "read_report", "报表读取", _tests_t4, _perf_t4),
    Task("T5", "find_bursts", "突发检测", _tests_t5, _perf_t5),
    Task("T6", "customer_spend", "客户消费", _tests_t6, _perf_t6),
    Task("T7", "category_totals", "类目汇总", _tests_t7, _perf_t7),
]
TASK_BY_KEY = {t.key: t for t in TASKS}
FUNC_NAMES = [t.fn for t in TASKS]

# ════════════════════════════════════════════════════════════════════════════
# 第 8 部分：子进程 worker（隔离运行候选代码）
# ════════════════════════════════════════════════════════════════════════════

def _load_impl(spec):
    if spec == "reference":
        return dict(REFERENCE)
    if spec == "baseline":
        mod = types.ModuleType("shop_utils_baseline")
        exec(compile(CHALLENGE_CODE, "shop_utils.py(原代码)", "exec"), mod.__dict__)
    else:
        mspec = importlib.util.spec_from_file_location("solution", spec)
        mod = importlib.util.module_from_spec(mspec)
        sys.modules["solution"] = mod
        mspec.loader.exec_module(mod)
    return {n: getattr(mod, n) for n in FUNC_NAMES if callable(getattr(mod, n, None))}


def _measure(fn, case):
    """返回 (单次耗时中位数, 首次输出的哈希, 计时次数)。快的实现会自动多跑几次以减少噪声。"""
    times, out_hash = [], None
    wall0 = time.perf_counter()
    while True:
        args = case.make()
        gc.collect()
        t0 = time.perf_counter()
        out = case.call(fn, args)
        times.append(time.perf_counter() - t0)
        if out_hash is None:
            out_hash = _hash(out)
        del out, args
        if sum(times) >= 0.3 or len(times) >= 25 or time.perf_counter() - wall0 > 4.0:
            break
    return statistics.median(times), out_hash, len(times)


def _worker_main(cfg):
    proto = os.fdopen(os.dup(sys.stdout.fileno()), "w", encoding="utf-8", buffering=1)
    sys.stdout.flush()
    os.dup2(sys.stderr.fileno(), sys.stdout.fileno())  # 候选代码的 print 一律进 stderr

    def send(obj):
        proto.write(json.dumps(obj, ensure_ascii=False) + "\n")
        proto.flush()

    try:
        impl = _load_impl(cfg["impl"])
    except BaseException:
        send({"type": "fatal", "error": traceback.format_exc(limit=6)})
        return
    if cfg["mode"] == "load":
        send({"type": "loaded", "functions": sorted(impl)})
        return
    task = TASK_BY_KEY[cfg["task"]]
    if cfg["mode"] == "tests":
        tests = task.build_tests()
        for i in range(cfg["start"], len(tests)):
            send({"type": "start", "i": i})
            t0 = time.perf_counter()
            try:
                status, msg = tests[i].run(impl, REFERENCE)
            except _MissingFunction as e:
                status, msg = "fail", "候选代码中没有定义函数 %s" % e
            except BaseException:
                status, msg = "fail", "测试过程中出现未处理的异常:\n" + traceback.format_exc(limit=4)
            send({"type": "result", "i": i, "status": status, "msg": msg, "sec": time.perf_counter() - t0})
        send({"type": "end"})
    else:
        fn = impl.get(task.fn)
        if fn is None:
            send({"type": "perf_error", "rep": 0, "error": "候选代码中没有定义函数 %s" % task.fn})
            return
        for rep in range(cfg["reps"]):
            send({"type": "start", "i": rep})
            case = task.perf(1000 + rep, cfg["scale"])
            try:
                sec, h, n = _measure(fn, case)
            except BaseException as e:
                send({"type": "perf_error", "rep": rep,
                      "error": _fmt_exc(e) + "\n" + traceback.format_exc(limit=3)})
                return
            finally:
                case.cleanup()
            send({"type": "perf", "rep": rep, "sec": sec, "hash": h, "iters": n})
        send({"type": "end"})


class _Worker:
    def __init__(self, cfg, item_timeout, boot_timeout=60.0):
        env = dict(os.environ)
        env["PYTHONDONTWRITEBYTECODE"] = "1"
        env["PYTHONIOENCODING"] = "utf-8"
        cmd = [sys.executable, os.path.abspath(__file__), "__worker__", json.dumps(cfg)]
        self.proc = subprocess.Popen(cmd, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
                                     stderr=subprocess.PIPE, env=env)
        self.item_timeout, self.boot_timeout = item_timeout, boot_timeout
        self.q = queue.Queue()
        self.err = collections.deque(maxlen=300)
        threading.Thread(target=self._pump_out, daemon=True).start()
        threading.Thread(target=self._pump_err, daemon=True).start()

    def _pump_out(self):
        for raw in iter(self.proc.stdout.readline, b""):
            self.q.put(raw)
        self.q.put(None)

    def _pump_err(self):
        for raw in iter(self.proc.stderr.readline, b""):
            self.err.append(raw.decode("utf-8", "replace"))

    def stderr_tail(self, limit=2500):
        return "".join(self.err)[-limit:]

    def kill(self):
        try:
            self.proc.kill()
            self.proc.wait(timeout=10)
        except Exception:
            pass

    def messages(self):
        deadline = time.monotonic() + self.boot_timeout
        while True:
            try:
                raw = self.q.get(timeout=max(0.01, deadline - time.monotonic()))
            except queue.Empty:
                self.kill()
                yield {"type": "timeout"}
                return
            if raw is None:
                try:
                    code = self.proc.wait(timeout=10)
                except subprocess.TimeoutExpired:
                    self.kill()
                    code = None
                time.sleep(0.05)
                yield {"type": "exit", "code": code}
                return
            try:
                msg = json.loads(raw.decode("utf-8"))
            except ValueError:
                continue
            deadline = time.monotonic() + self.item_timeout
            yield msg


def _condense_tb(tb_text, impl_path):
    """只保留候选代码自己的出错位置和异常信息，去掉评测器内部的调用栈。"""
    lines = tb_text.rstrip().splitlines()
    for i in range(len(lines) - 1, -1, -1):
        if impl_path in lines[i] and lines[i].lstrip().startswith("File "):
            return "\n".join(ln.rstrip() for ln in lines[i:])
    return "\n".join(lines[-4:])


def check_load(impl_spec, timeout=30.0):
    """先单独加载一次候选代码：语法错误、导入即崩溃、模块顶层死循环等问题直接判定，不必每个任务都等超时。"""
    w = _Worker({"impl": impl_spec, "mode": "load"}, timeout, boot_timeout=timeout)
    for msg in w.messages():
        t = msg["type"]
        if t == "loaded":
            return None, msg["functions"]
        if t == "fatal":
            return "候选代码无法加载:\n" + _condense_tb(msg["error"], impl_spec), []
        if t == "timeout":
            return "候选代码加载超时（> %.0fs）：模块顶层可能有死循环或耗时操作" % timeout, []
        if t == "exit":
            return "加载候选代码时子进程退出（退出码 %s）:\n%s" % (msg["code"], w.stderr_tail(800)), []
    return "加载候选代码失败（未知原因）", []


def run_tests(impl_spec, task, test_timeout):
    tests = task.build_tests()
    n = len(tests)
    results = [None] * n
    stderr_tail = ""
    start = 0
    streak = 0  # 连续超时次数
    while start < n:
        if streak >= 3:
            for i in range(start, n):
                results[i] = ("fail", "前面连续 3 个测试超时，余下测试不再运行（按失败计）", 0.0)
            break
        w = _Worker({"impl": impl_spec, "task": task.key, "mode": "tests", "start": start}, test_timeout)
        current = None
        for msg in w.messages():
            t = msg["type"]
            if t == "fatal":
                for i in range(start, n):
                    results[i] = ("fail", "候选代码无法加载:\n" + msg["error"], 0.0)
                return tests, results, w.stderr_tail()
            if t == "start":
                current = msg["i"]
            elif t == "result":
                results[msg["i"]] = (msg["status"], msg["msg"], msg["sec"])
                current, start, streak = None, msg["i"] + 1, 0
            elif t == "end":
                start = n
            elif t == "timeout":
                idx = current if current is not None else start
                results[idx] = ("fail", "超时（单个测试超过 %gs）：可能死循环、复杂度过高或在做危险的计算" % test_timeout,
                                float(test_timeout))
                start, streak = idx + 1, streak + 1
            elif t == "exit":
                if current is not None:
                    results[current] = ("fail", "子进程崩溃（退出码 %s），可能是栈溢出 / 段错误 / 调用了 sys.exit:\n%s"
                                        % (msg["code"], w.stderr_tail(800)), 0.0)
                    start = current + 1
                elif start < n:
                    for i in range(start, n):
                        results[i] = ("fail", "子进程意外退出（退出码 %s）:\n%s" % (msg["code"], w.stderr_tail(800)), 0.0)
                    start = n
        stderr_tail = w.stderr_tail()
    return tests, results, stderr_tail


def run_perf(impl_spec, task, reps, scale, timeout):
    w = _Worker({"impl": impl_spec, "task": task.key, "mode": "perf", "reps": reps, "scale": scale}, timeout)
    reps_out = []
    for msg in w.messages():
        t = msg["type"]
        if t == "fatal":
            return {"error": "代码无法加载: " + msg["error"].strip().splitlines()[-1]}
        if t == "perf":
            reps_out.append(msg)
        elif t == "perf_error":
            return {"error": "大数据量运行时出错: " + msg["error"].strip()}
        elif t == "timeout":
            return {"error": "大数据量运行超时（> %.0fs）" % timeout}
        elif t == "exit":
            if len(reps_out) < reps:
                return {"error": "子进程崩溃（退出码 %s）: %s" % (msg["code"], w.stderr_tail(500))}
    return {"reps": reps_out, "sec": statistics.median(r["sec"] for r in reps_out),
            "hashes": [r["hash"] for r in reps_out]}


# ════════════════════════════════════════════════════════════════════════════
# 第 9 部分：静态审查（只给提示，不扣分）
# ════════════════════════════════════════════════════════════════════════════

def static_review(src):
    notes = []
    try:
        tree = ast.parse(src)
    except SyntaxError as e:
        return ["代码有语法错误: %s" % e]
    top_defs = {n.name for n in tree.body if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef))}
    missing = [f for f in FUNC_NAMES if f not in top_defs]
    if missing:
        notes.append("缺少（或不是模块顶层定义的）函数: %s" % ", ".join(missing))
    stdlib = getattr(sys, "stdlib_module_names", None)
    risky_mods = {"subprocess": "subprocess", "pickle": "pickle", "marshal": "marshal", "ctypes": "ctypes",
                  "multiprocessing": "多进程", "shelve": "shelve"}
    for node in ast.walk(tree):
        line = getattr(node, "lineno", "?")
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
            for d in list(node.args.defaults) + [d for d in node.args.kw_defaults if d is not None]:
                if isinstance(d, (ast.List, ast.Dict, ast.Set)) or (
                        isinstance(d, ast.Call) and isinstance(d.func, ast.Name)
                        and d.func.id in ("list", "dict", "set", "defaultdict", "OrderedDict")):
                    notes.append("第 %s 行：%s 使用了可变默认参数（跨调用共享状态）"
                                 % (line, getattr(node, "name", "lambda")))
        elif isinstance(node, ast.ExceptHandler):
            if node.type is None:
                notes.append("第 %s 行：裸 except:，会吞掉所有异常（包括 KeyboardInterrupt）" % line)
            elif isinstance(node.type, ast.Name) and node.type.id == "BaseException":
                notes.append("第 %s 行：捕获 BaseException" % line)
            if len(node.body) == 1 and isinstance(node.body[0], ast.Pass):
                notes.append("第 %s 行：异常被静默吞掉（except ...: pass）" % line)
        elif isinstance(node, ast.Call):
            f = node.func
            if isinstance(f, ast.Name) and f.id in ("eval", "exec"):
                notes.append("第 %s 行：调用了 %s()，请人工确认是否只执行经过严格白名单校验的内容" % (line, f.id))
            if isinstance(f, ast.Attribute) and isinstance(f.value, ast.Name):
                full = "%s.%s" % (f.value.id, f.attr)
                if full in ("os.system", "os.popen"):
                    notes.append("第 %s 行：调用了 %s" % (line, full))
                if full == "sys.setrecursionlimit":
                    notes.append("第 %s 行：调高了递归上限（深递归仍可能导致 C 栈溢出崩溃）" % line)
        elif isinstance(node, ast.Global):
            notes.append("第 %s 行：使用了 global 变量 %s（注意跨调用状态）" % (line, ", ".join(node.names)))
        elif isinstance(node, (ast.Import, ast.ImportFrom)):
            mods = [a.name for a in node.names] if isinstance(node, ast.Import) else [node.module or ""]
            for m in mods:
                top = m.split(".")[0]
                if not top:
                    continue
                if top in risky_mods:
                    notes.append("第 %s 行：导入了 %s" % (line, risky_mods[top]))
                if stdlib is not None and top not in stdlib:
                    notes.append("第 %s 行：导入了非标准库模块 %s（违反题目要求）" % (line, m))
    if "ai_code_bench" in src or "_ref_" in src:
        notes.append("代码中出现了评测器内部名称（ai_code_bench / _ref_），疑似直接引用了参考答案")
    seen, uniq = set(), []
    for n in notes:
        if n not in seen:
            seen.add(n)
            uniq.append(n)
    return uniq


# ════════════════════════════════════════════════════════════════════════════
# 第 10 部分：判卷与报告
# ════════════════════════════════════════════════════════════════════════════

W_FUNC, W_HIDDEN, W_PERF = 40.0, 30.0, 30.0


def _perf_ratio(s, r):
    if s is None or s <= 1.0:
        return 0.0
    if r <= 1.05:
        return 1.0 if s >= 0.95 * r else max(0.0, s / r)
    return max(0.0, min(1.0, math.log(s) / math.log(r)))


def score_task(tests, results, perf_c, perf_b, perf_r):
    groups = {"func": [0.0, 0.0], "hidden": [0.0, 0.0]}
    sec_ok = True
    for t, (status, _msg, _sec) in zip(tests, results):
        if status == "skip":
            continue
        if t.cat == "安全" and status != "pass":
            sec_ok = False
        g = groups["func" if t.cat == "功能" else "hidden"]
        g[1] += t.weight
        if status == "pass":
            g[0] += t.weight
    func_ok = groups["func"][0] == groups["func"][1]
    s_func = W_FUNC * groups["func"][0] / groups["func"][1] if groups["func"][1] else W_FUNC
    s_hidden = W_HIDDEN * groups["hidden"][0] / groups["hidden"][1] if groups["hidden"][1] else W_HIDDEN

    perf = {"base": perf_b.get("sec"), "ref": perf_r.get("sec"), "cand": perf_c.get("sec"),
            "speedup": None, "ref_speedup": None, "note": "", "valid": False}
    if perf["base"] and perf["ref"]:
        perf["ref_speedup"] = perf["base"] / perf["ref"]
    s_perf = 0.0
    if perf_b.get("error") or perf_r.get("error"):
        perf["note"] = "基准测量失败: %s" % (perf_b.get("error") or perf_r.get("error"))
    elif perf_c.get("error"):
        perf["note"] = perf_c["error"]
    else:
        perf["speedup"] = perf["base"] / perf["cand"] if perf["cand"] else None
        if perf_c["hashes"] != perf_r["hashes"]:
            perf["note"] = "大数据量上的输出与参考答案不一致，性能分不计"
        elif not func_ok:
            perf["valid"] = True
            perf["note"] = "功能测试未全部通过，性能分不计"
        elif not sec_ok:
            perf["valid"] = True
            perf["note"] = "存在未修复的安全漏洞，性能分不计"
        else:
            perf["valid"] = True
            s_perf = W_PERF * _perf_ratio(perf["speedup"], perf["ref_speedup"] or 1.0)
            if perf["speedup"] is not None and perf["speedup"] < 1:
                perf["note"] = "比原代码更慢"
    return {"func": groups["func"], "hidden": groups["hidden"], "perf": perf,
            "score": {"func": s_func, "hidden": s_hidden, "perf": s_perf, "total": s_func + s_hidden + s_perf}}


def _dw(s):
    return sum(2 if unicodedata.east_asian_width(ch) in "WF" else 1 for ch in s)


def _pad(s, width, right=False):
    s = str(s)
    gap = " " * max(0, width - _dw(s))
    return gap + s if right else s + gap


def _ft(sec):
    if sec is None:
        return "-"
    if sec >= 1:
        return "%.2fs" % sec
    if sec >= 1e-3:
        return "%.1fms" % (sec * 1e3)
    return "%.0fµs" % (sec * 1e6)


def _fx(x):
    if x is None:
        return "-"
    return ("%.0fx" % x) if x >= 100 else ("%.1fx" % x) if x >= 10 else ("%.2fx" % x)


def _geomean(xs):
    xs = [x for x in xs if x and x > 0]
    return math.exp(sum(math.log(x) for x in xs) / len(xs)) if xs else None


class Candidate:
    def __init__(self, label, impl, source, notes, extracted_from=None):
        self.label, self.impl, self.source, self.notes = label, impl, source, notes
        self.extracted_from = extracted_from
        self.load_error = None
        self.results = {}
        self.stderr = {}


def _extract_code(text):
    try:
        ast.parse(text)
        return text, False
    except SyntaxError:
        pass
    blocks = re.findall(r"```[ \t]*(?:python3?|py)?[^\n]*\n(.*?)```", text, re.S)
    if not blocks:
        return text, False
    best = max(blocks, key=lambda b: (sum(("def %s(" % f) in b for f in FUNC_NAMES), len(b)))
    return best, True


def load_candidate(path):
    if path in ("@baseline", "@reference"):
        impl = path[1:]
        src = CHALLENGE_CODE if impl == "baseline" else None
        label = "原代码(@baseline)" if impl == "baseline" else "参考答案(@reference)"
        return Candidate(label, impl, src, static_review(src) if src else [])
    with open(path, "r", encoding="utf-8", errors="replace") as f:
        text = f.read()
    code, extracted = _extract_code(text)
    impl_path = os.path.abspath(path)
    if extracted or not path.endswith(".py"):
        root, _ = os.path.splitext(impl_path)
        impl_path = root + ".extracted.py"
        with open(impl_path, "w", encoding="utf-8") as f:
            f.write(code)
    return Candidate(os.path.basename(path), impl_path, code, static_review(code),
                     extracted_from=path if impl_path != os.path.abspath(path) else None)


def judge(cands, tasks, scale, reps, test_timeout, log=functools.partial(print, flush=True)):
    for c in cands:
        c.load_error, functions = check_load(c.impl)
        if c.load_error:
            log("✗ %s：%s" % (c.label, c.load_error.splitlines()[0]))
        elif set(FUNC_NAMES) - set(functions):
            log("⚠ %s：缺少函数 %s" % (c.label, ", ".join(sorted(set(FUNC_NAMES) - set(functions)))))
    for task in tasks:
        log("\n▶ %s（%s）" % (task.label, task.title))
        log("  计时 原代码 ……", end="")
        perf_b = run_perf("baseline", task, reps, scale, timeout=300)
        log(" %s" % (_ft(perf_b.get("sec")) if "sec" in perf_b else perf_b.get("error")), end="")
        log("  | 参考答案 ……", end="")
        perf_r = run_perf("reference", task, reps, scale, timeout=120)
        log(" %s" % (_ft(perf_r.get("sec")) if "sec" in perf_r else perf_r.get("error")))
        cand_timeout = max(30.0, 5 * (perf_b.get("sec") or 10.0) + 10)
        for c in cands:
            if c.load_error:
                tests, err = task.build_tests(), ""
                results = [("fail", c.load_error, 0.0)] * len(tests)
                perf_c = {"error": "候选代码无法加载"}
            else:
                tests, results, err = run_tests(c.impl, task, test_timeout)
                perf_c = run_perf(c.impl, task, reps, scale, timeout=cand_timeout)
            res = score_task(tests, results, perf_c, perf_b, perf_r)
            res["tests"] = [{"id": t.id, "cat": t.cat, "desc": t.desc, "weight": t.weight,
                             "status": r[0], "msg": r[1], "sec": r[2]} for t, r in zip(tests, results)]
            c.results[task.key] = res
            c.stderr[task.key] = err
            n_pass = sum(1 for r in results if r[0] == "pass")
            n_skip = sum(1 for r in results if r[0] == "skip")
            p = res["perf"]
            log("  %s 测试 %d/%d 通过%s | 耗时 %s | 加速 %s（参考 %s）| 得分 %.1f%s" % (
                _pad(c.label, 22), n_pass, len(results) - n_skip, "（%d 跳过）" % n_skip if n_skip else "",
                _ft(p["cand"]), _fx(p["speedup"]), _fx(p["ref_speedup"]), res["score"]["total"],
                ("  ⚠ " + p["note"].splitlines()[0]) if p["note"] else ""))
    return cands


def _summary(c, tasks):
    """返回 (总分, 候选几何平均加速比, 参考答案在同一批任务上的几何平均加速比, 有效任务数)。"""
    totals = [c.results[t.key]["score"]["total"] for t in tasks]
    valid = [c.results[t.key]["perf"] for t in tasks if c.results[t.key]["perf"]["valid"]]
    return (sum(totals) / len(totals), _geomean([p["speedup"] for p in valid]),
            _geomean([p["ref_speedup"] for p in valid]), len(valid))


def print_report(c, tasks, verbose=False):
    line = "═" * 100
    print("\n" + line)
    print(" 评测报告：%s%s" % (c.label, "（代码提取自 %s → %s）" % (c.extracted_from, c.impl) if c.extracted_from else ""))
    print(line)
    cols = [("任务", 26, False), ("功能", 8, True), ("安全/隐性", 10, True), ("原代码", 9, True),
            ("参考答案", 9, True), ("候选", 9, True), ("加速比", 8, True), ("参考加速", 9, True),
            ("功能", 6, True), ("隐性", 6, True), ("性能", 6, True), ("得分", 7, True)]
    print("".join(_pad(h, w, r) + " " for h, w, r in cols))
    print("─" * 100)
    for t in tasks:
        r = c.results[t.key]
        p, s = r["perf"], r["score"]
        f_pass = sum(1 for x in r["tests"] if x["cat"] == "功能" and x["status"] == "pass")
        f_all = sum(1 for x in r["tests"] if x["cat"] == "功能" and x["status"] != "skip")
        h_pass = sum(1 for x in r["tests"] if x["cat"] != "功能" and x["status"] == "pass")
        h_all = sum(1 for x in r["tests"] if x["cat"] != "功能" and x["status"] != "skip")
        sp = _fx(p["speedup"]) + ("" if p["valid"] or p["speedup"] is None else "✗")
        row = ["%s %s" % (t.label, t.title), "%d/%d" % (f_pass, f_all), "%d/%d" % (h_pass, h_all),
               _ft(p["base"]), _ft(p["ref"]), _ft(p["cand"]), sp, _fx(p["ref_speedup"]),
               "%.1f" % s["func"], "%.1f" % s["hidden"], "%.1f" % s["perf"], "%.1f" % s["total"]]
        print("".join(_pad(v, w, rr) + " " for v, (_h, w, rr) in zip(row, cols)))
    print("─" * 100)
    total, gm, gm_ref, n_valid = _summary(c, tasks)
    print(" 总分 %.1f / 100    （功能 %d + 安全/隐性 %d + 性能 %d，每个任务满分 100，总分为平均值）"
          % (total, W_FUNC, W_HIDDEN, W_PERF))
    print(" 几何平均加速比 %s（参考答案在相同任务上 %s；统计了大数据输出正确的 %d/%d 个任务）"
          % (_fx(gm), _fx(gm_ref), n_valid, len(tasks)))
    print(" 加速比后的 ✗ 表示该任务在大数据量上的输出不正确")
    if c.load_error:
        print("\n ✗ 候选代码无法运行，所有测试按失败计:")
        for ln in c.load_error.splitlines()[:20]:
            print("    " + ln)
        notes = []
    else:
        notes = [(t, c.results[t.key]["perf"]["note"]) for t in tasks if c.results[t.key]["perf"]["note"]]
    if notes:
        print("\n 性能备注:")
        for t, n in notes:
            print("  - %s: %s" % (t.label, n.splitlines()[0] if n else ""))
    fails = [(t, x) for t in tasks for x in c.results[t.key]["tests"] if x["status"] == "fail"]
    if c.load_error:
        pass
    elif fails:
        print("\n ✗ 未通过的测试（%d 项）:" % len(fails))
        for t, x in fails:
            print("  [%s %s] %s" % (x["id"], x["cat"], x["desc"]))
            for ln in (x["msg"] or "").splitlines()[:14]:
                print("      " + ln)
    else:
        print("\n ✓ 所有测试均通过")
    skips = [x for t in tasks for x in c.results[t.key]["tests"] if x["status"] == "skip"]
    for x in skips:
        print("  (跳过) [%s] %s：%s" % (x["id"], x["desc"], x["msg"]))
    if verbose:
        print("\n 通过的测试:")
        for t in tasks:
            for x in c.results[t.key]["tests"]:
                if x["status"] == "pass":
                    print("  ✓ [%s %s] %s（%s）" % (x["id"], x["cat"], x["desc"], _ft(x["sec"])))
        for k, err in c.stderr.items():
            if err.strip():
                print("\n --- %s 候选代码 stderr（末尾）---\n%s" % (k, err))
    if c.notes:
        print("\n 静态审查提示（不计分，供人工复核）:")
        for n in c.notes:
            print("  - " + n)
    print(line)


def print_comparison(cands, tasks):
    print("\n" + "═" * 100)
    print(" 多模型对比")
    print("═" * 100)
    head = [("候选", 28, False)] + [(t.key, 8, True) for t in tasks] + [("总分", 8, True), ("几何加速", 10, True)]
    print("".join(_pad(h, w, r) + " " for h, w, r in head))
    for c in sorted(cands, key=lambda c: -_summary(c, tasks)[0]):
        total, gm, _, _ = _summary(c, tasks)
        row = [c.label] + ["%.1f" % c.results[t.key]["score"]["total"] for t in tasks] + ["%.1f" % total, _fx(gm)]
        print("".join(_pad(v, w, r) + " " for v, (_h, w, r) in zip(row, head)))


def write_markdown(cands, tasks, path, meta):
    out = ["# AI 代码修复与优化评测报告", "",
           "- 评测器版本: %s，Python %s，%s" % (BENCH_VERSION, sys.version.split()[0], sys.platform),
           "- 计时: 每个实现 %d 轮取中位数，数据规模系数 %.2f" % (meta["reps"], meta["scale"]),
           "- 计分: 每个任务 100 分 = 功能 %d + 安全/隐性 %d + 性能 %d；性能分 = %d × ln(加速比)/ln(参考加速比)，"
           "上限 %d；功能测试未全过、存在安全漏洞或大数据输出错误时性能分为 0。" % (W_FUNC, W_HIDDEN, W_PERF, W_PERF, W_PERF), ""]
    if len(cands) > 1:
        out += ["## 总览", "", "| 候选 | " + " | ".join(t.key for t in tasks) + " | 总分 | 几何加速 |",
                "|---|" + "---|" * (len(tasks) + 2)]
        for c in sorted(cands, key=lambda c: -_summary(c, tasks)[0]):
            total, gm, _, _ = _summary(c, tasks)
            out.append("| %s | %s | **%.1f** | %s |" % (
                c.label, " | ".join("%.1f" % c.results[t.key]["score"]["total"] for t in tasks), total, _fx(gm)))
        out.append("")
    for c in cands:
        total, gm, gm_ref, n_valid = _summary(c, tasks)
        out += ["## %s —— 总分 %.1f / 100" % (c.label, total), "",
                "几何平均加速比 **%s**（参考答案在相同任务上 %s；统计了 %d/%d 个大数据输出正确的任务）"
                % (_fx(gm), _fx(gm_ref), n_valid, len(tasks)), "",
                "| 任务 | 功能 | 安全/隐性 | 原代码 | 参考 | 候选 | 加速比 | 参考加速 | 得分 | 备注 |",
                "|---|---|---|---|---|---|---|---|---|---|"]
        for t in tasks:
            r = c.results[t.key]
            p = r["perf"]
            fa = [x for x in r["tests"] if x["cat"] == "功能" and x["status"] != "skip"]
            ha = [x for x in r["tests"] if x["cat"] != "功能" and x["status"] != "skip"]
            out.append("| %s %s | %d/%d | %d/%d | %s | %s | %s | %s | %s | %.1f | %s |" % (
                t.label, t.title, sum(x["status"] == "pass" for x in fa), len(fa),
                sum(x["status"] == "pass" for x in ha), len(ha), _ft(p["base"]), _ft(p["ref"]), _ft(p["cand"]),
                _fx(p["speedup"]), _fx(p["ref_speedup"]), r["score"]["total"],
                (p["note"] or "").splitlines()[0].replace("|", "\\|") if p["note"] else ""))
        fails = [x for t in tasks for x in c.results[t.key]["tests"] if x["status"] == "fail"]
        if c.load_error:
            out += ["", "### 候选代码无法运行", "", "```text"] + c.load_error.splitlines()[:20] + ["```", ""]
            fails = []
        out += ["", "### 未通过的测试（%d 项）" % len(fails), ""]
        for x in fails:
            out += ["- **[%s %s] %s**" % (x["id"], x["cat"], x["desc"]), "", "  ```text"]
            out += ["  " + ln for ln in (x["msg"] or "").splitlines()[:14]]
            out += ["  ```", ""]
        if not fails:
            out.append("全部通过。")
        if c.notes:
            out += ["", "### 静态审查提示（不计分）", ""] + ["- " + n for n in c.notes]
        out.append("")
    with open(path, "w", encoding="utf-8") as f:
        f.write("\n".join(out))


def write_json(cands, tasks, path, meta):
    data = {"version": BENCH_VERSION, "python": sys.version.split()[0], "meta": meta, "candidates": []}
    for c in cands:
        total, gm, gm_ref, n_valid = _summary(c, tasks)
        data["candidates"].append({"label": c.label, "total": total, "geomean_speedup": gm,
                                   "geomean_ref_speedup": gm_ref, "perf_valid_tasks": n_valid,
                                   "load_error": c.load_error, "static_notes": c.notes,
                                   "tasks": {t.key: c.results[t.key] for t in tasks}})
    with open(path, "w", encoding="utf-8") as f:
        json.dump(data, f, ensure_ascii=False, indent=2)


# ════════════════════════════════════════════════════════════════════════════
# 第 11 部分：自检（出题官审核自己的标准答案）
# ════════════════════════════════════════════════════════════════════════════

def _crosscheck(rounds=300):
    """用彼此独立的朴素实现，与参考答案随机对拍。返回不一致的描述列表。"""
    from decimal import Decimal, ROUND_HALF_UP
    rng = random.Random(20261021)
    bad = []

    def naive_t1(orders, k):
        cnt = collections.Counter()
        for o in orders:
            for it in o["items"]:
                cnt[it["sku"]] += it["qty"]
        return sorted(((s, n) for s, n in cnt.items() if n > 0), key=lambda p: (-p[1], p[0]))[:max(k, 0)]

    def naive_t2(orders, coupons):
        out = {}
        for o in orders:
            sub = sum((it["qty"] * Decimal(it["unit_price"]) for it in o["items"]), Decimal(0))
            disc = Decimal(0)
            code = o.get("coupon")
            if code is not None:
                for c in coupons:
                    if c["code"] == code and sub >= Decimal(c["min_subtotal"]):
                        disc = (sub * c["percent_off"] / 100).quantize(Decimal("0.01"), rounding=ROUND_HALF_UP)
            out[o["order_id"]] = str((sub - disc).quantize(Decimal("0.01")))
        return out

    def naive_t5(events, window, threshold):
        res = set()
        for u in {e[0] for e in events}:
            ts = sorted(t for uu, t in events if uu == u)
            if any(sum(1 for t2 in ts if t <= t2 < t + window) >= threshold for t in ts):
                res.add(u)
        return sorted(res)

    def naive_t7(parent_of, sales):
        totals = {n: 0 for n in parent_of}
        for n in parent_of:
            seen, cur = set(), n
            while cur is not None:
                if cur in seen:
                    raise ValueError("cycle")
                seen.add(cur)
                totals[cur] += sales.get(n, 0)
                cur = parent_of[cur]
        return totals

    def naive_t6(rows, names):
        conn = _make_db(rows)
        try:
            return {n: conn.execute("SELECT COALESCE(SUM(amount_cents), 0) FROM orders WHERE customer = ?",
                                    (n,)).fetchone()[0] for n in names}
        finally:
            conn.close()

    def naive_t3(expr, variables):
        if len(expr) > 200:
            raise ValueError
        try:
            return eval(expr.strip(" \t"), {"__builtins__": {}}, dict(variables))  # 仅用于对拍随机生成的合法表达式
        except ArithmeticError:
            raise ValueError

    def cmp(name, a_fn, b_fn, args):
        oa, ob = _outcome(a_fn, copy.deepcopy(args)), _outcome(b_fn, copy.deepcopy(args))
        if oa[0] != ob[0] or (oa[0] == "ok" and not _same(oa[1], ob[1])) or \
                (oa[0] == "exc" and type(oa[1]) is not type(ob[1])):
            bad.append("%s 不一致: 输入=%s 参考=%s 朴素=%s" % (name, _short(args, 200), _short(oa, 120), _short(ob, 120)))

    for _ in range(rounds):
        cmp("T1", _ref_top_skus, naive_t1, _rand_t1(rng))
        cmp("T2", _ref_order_totals, naive_t2, _rand_t2(rng))
        cmp("T3", _ref_eval_rule, naive_t3, _rand_t3(rng))
        cmp("T5", _ref_find_bursts, naive_t5, _rand_t5(rng))
        cmp("T7", _ref_category_totals, naive_t7, _rand_t7(rng))
        rows, names = _rand_t6(rng)
        conn = _make_db(rows)
        try:
            got = _ref_customer_spend(conn, names)
        finally:
            conn.close()
        exp = naive_t6(rows, names)
        if not _same(got, exp):
            bad.append("T6 不一致: rows=%s names=%s 参考=%s 朴素=%s" % (_short(rows), names, got, exp))
    # 性能数据集（小规模）上参考答案也要与朴素实现一致
    for task, naive in (("T1", naive_t1), ("T2", naive_t2), ("T5", naive_t5), ("T7", naive_t7)):
        outs = []
        for fn in (REFERENCE[TASK_BY_KEY[task].fn], naive):
            case = TASK_BY_KEY[task].perf(1000, 0.05)  # 每个实现各用一份新数据（make() 有计数器）
            try:
                outs.append(case.call(fn, case.make()))
            finally:
                case.cleanup()
        if not _same(outs[0], outs[1]):
            bad.append("%s 性能数据集上参考答案与朴素实现不一致" % task)
    return bad


def cmd_selftest(args):
    t0 = time.time()
    print("【1/3】参考答案 vs 独立朴素实现，随机对拍 ……", end="", flush=True)
    bad = _crosscheck(300)
    print(" %s" % ("通过" if not bad else "发现 %d 处不一致" % len(bad)))
    for b in bad[:10]:
        print("   ", b)
    scale, reps = (1.0, 3) if args.full else (0.3, 1)
    print("【2/3】把参考答案和原代码当作候选，跑完整评测（性能数据规模 %.1f）……" % scale)
    cands = [load_candidate("@reference"), load_candidate("@baseline")]
    judge(cands, TASKS, scale, reps, args.timeout)
    ref_c, base_c = cands
    print_report(ref_c, TASKS)
    print_report(base_c, TASKS)
    print("【3/3】核对自检结论 ……")
    problems = list(bad)
    for t in TASKS:
        rr, br = ref_c.results[t.key], base_c.results[t.key]
        failed = [x for x in rr["tests"] if x["status"] == "fail"]
        if failed:
            problems.append("%s: 参考答案未通过 %s" % (t.label, ", ".join(x["id"] for x in failed)))
        if not rr["perf"]["valid"]:
            problems.append("%s: 参考答案性能测量异常: %s" % (t.label, rr["perf"]["note"]))
        if (rr["perf"]["ref_speedup"] or 0) < 2:
            problems.append("%s: 参考答案相对原代码的加速不足 2 倍（%s）" % (t.label, _fx(rr["perf"]["ref_speedup"])))
        b_fail = [x for x in br["tests"] if x["status"] == "fail"]
        if not b_fail:
            problems.append("%s: 原代码没有暴露任何问题" % t.label)
        else:
            cats = sorted({x["cat"] for x in b_fail})
            print("  %s 原代码未通过 %d 项（%s）" % (_pad(t.label, 20), len(b_fail), "、".join(cats)))
    print("\n耗时 %.0fs" % (time.time() - t0))
    if problems:
        print("✗ 自检失败:")
        for p in problems:
            print("  - " + p)
        return 1
    print("✓ 自检通过：参考答案全部测试通过且与朴素实现一致，原代码在每个任务上都被测出问题。")
    return 0


# ════════════════════════════════════════════════════════════════════════════
# 第 12 部分：命令行
# ════════════════════════════════════════════════════════════════════════════

def _select_tasks(only):
    if not only:
        return list(TASKS)
    keys = [k.strip().upper() for k in only.split(",") if k.strip()]
    by_fn = {t.fn: t for t in TASKS}
    out = []
    for k in keys:
        t = TASK_BY_KEY.get(k) or by_fn.get(k.lower())
        if t is None:
            raise SystemExit("未知任务: %s（可选 %s）" % (k, ", ".join(TASK_BY_KEY)))
        out.append(t)
    return out


def cmd_prompt(args):
    text = build_prompt()
    if args.output:
        with open(args.output, "w", encoding="utf-8") as f:
            f.write(text)
        print("题目已写入 %s（%d 字符）。把它的全部内容发给被测模型即可。" % (args.output, len(text)))
    else:
        sys.stdout.write(text)
    return 0


def cmd_judge(args):
    tasks = _select_tasks(args.only)
    scale = args.scale if args.scale else (0.35 if args.quick else 1.0)
    reps = args.reps if args.reps else (1 if args.quick else 3)
    cands = []
    for p in args.paths:
        if not p.startswith("@") and not os.path.isfile(p):
            raise SystemExit("找不到文件: %s" % p)
        c = load_candidate(p)
        if c.extracted_from:
            print("已从 %s 中提取 Python 代码 → %s" % (p, c.impl))
        cands.append(c)
    print("AI 代码修复与优化评测 v%s | Python %s | 数据规模 ×%.2f | 每个实现计时 %d 轮"
          % (BENCH_VERSION, sys.version.split()[0], scale, reps))
    judge(cands, tasks, scale, reps, args.timeout)
    for c in cands:
        print_report(c, tasks, args.verbose)
    if len(cands) > 1:
        print_comparison(cands, tasks)
    meta = {"scale": scale, "reps": reps, "tasks": [t.key for t in tasks]}
    if args.report:
        write_markdown(cands, tasks, args.report, meta)
        print("\nMarkdown 报告已写入 %s" % args.report)
    if args.json:
        write_json(cands, tasks, args.json, meta)
        print("JSON 结果已写入 %s" % args.json)
    return 0


def main(argv=None):
    argv = sys.argv[1:] if argv is None else argv
    if argv and argv[0] == "__worker__":
        _worker_main(json.loads(argv[1]))
        return 0
    for stream in (sys.stdout, sys.stderr):
        try:
            stream.reconfigure(encoding="utf-8")
        except (AttributeError, ValueError):
            pass
    ap = argparse.ArgumentParser(description="AI 代码修复与性能优化评测器（出题 + 判卷）")
    sub = ap.add_subparsers(dest="cmd")
    p = sub.add_parser("prompt", help="生成发给模型的题目")
    p.add_argument("-o", "--output", help="写入文件（默认打印到屏幕）")
    j = sub.add_parser("judge", help="评测一个或多个候选答案")
    j.add_argument("paths", nargs="+", help="solution.py / 模型完整回复 .md；@baseline、@reference 为内置实现")
    j.add_argument("--quick", action="store_true", help="小规模数据、单轮计时")
    j.add_argument("--reps", type=int, default=0, help="每个实现计时轮数（默认 3）")
    j.add_argument("--scale", type=float, default=0.0, help="性能数据规模系数（默认 1.0）")
    j.add_argument("--only", help="只评测部分任务，如 T1,T3 或 eval_rule")
    j.add_argument("--timeout", type=float, default=15.0, help="单个测试的超时秒数（默认 15）")
    j.add_argument("--report", help="输出 Markdown 报告路径")
    j.add_argument("--json", help="输出 JSON 结果路径")
    j.add_argument("-v", "--verbose", action="store_true")
    s = sub.add_parser("selftest", help="评测器自检")
    s.add_argument("--full", action="store_true", help="使用完整规模的性能数据")
    s.add_argument("--timeout", type=float, default=15.0)
    args = ap.parse_args(argv)
    if args.cmd == "prompt":
        return cmd_prompt(args)
    if args.cmd == "judge":
        return cmd_judge(args)
    if args.cmd == "selftest":
        return cmd_selftest(args)
    ap.print_help()
    return 0


if __name__ == "__main__":
    sys.exit(main())
