#!/usr/bin/env python3
# -*- coding: utf-8 -*-
r"""
AI 代码修复 & 性能优化评测器 v2（高难度版，单文件，仅依赖 Python 3.8+ 标准库）

v1 对顶尖模型区分度不够（强模型普遍 99+ 分）。v2 的设计目标是在顶尖模型之间拉开差距：
  - 算法上限高：正确但普通的解法与最优解法相差 10~1000 倍，并有“最坏情况”计时测试；
  - 规格稠密：大量相互作用的精确规则，读漏任何一条都会在定向测试和随机对拍中暴露；
  - 隐性/安全陷阱：ReDoS、十亿笑声式展开、10 万层嵌套、多线程竞争、精度、惰性求值……
  - 性能加分：比参考实现（出题人的标准答案）快 10% 以上开始加分，之后每快一倍 +10 分，最多 +20 分。

用法：
  python ai_code_bench_v2.py prompt -o prompt_v2.md        生成题目，把内容发给被测模型
  python ai_code_bench_v2.py judge a.py b.md ...            评测（可直接传模型的整段回复 .md）
  python ai_code_bench_v2.py judge a.py --report r.md       额外输出 Markdown 报告（--json 输出 JSON）
  python ai_code_bench_v2.py selftest                       评测器自检
  python ai_code_bench_v2.py judge @baseline @reference     评测原代码 / 内置参考答案

常用选项（judge）：--quick 小规模单轮计时；--reps N；--only T1,T3；--timeout 秒；-v

计分：每个任务 100 分 = 功能 35 + 安全/隐性 35 + 性能 30，另有最多 +20 性能加分。
  性能基础分 = 30 × ln(相对原代码的加速比) / ln(参考实现的加速比)，最多 30；
  加分 = 10 × log2(参考实现耗时 / 候选耗时 / 1.1)，最多 +20（快不到 10% 视为计时噪声，不加分）；
  性能分（含加分）再乘以功能测试通过率；任一安全测试失败时性能分为 0；大数据输出不正确时性能分减半且无加分。
  最坏情况计时测试：超时不得分；没超时但结果错误得一半分（正确性由功能测试另行扣分）。
  总分 = 各任务得分的平均值（满分 100，含加分最高 120）。

注意：不要把本文件发给被测模型——它包含参考答案和全部隐藏测试。只发 prompt 命令生成的内容。
本评测器面向“正常作答”的模型；候选代码与测试运行在同一子进程中，并不能防御刻意针对评测器的攻击。
"""

import argparse
import ast
import bisect
import collections
import copy
import functools
import gc
import hashlib
import heapq
import importlib.util
import itertools
import json
import math
import os
import queue
import random
import re
import statistics
import subprocess
import sys
import threading
import time
import traceback
import tracemalloc
import types
import unicodedata

BENCH_VERSION = "2.0"

# ════════════════════════════════════════════════════════════════════════════
# 第 1 部分：题目 —— 祖传代码
# ════════════════════════════════════════════════════════════════════════════

CHALLENGE_CODE = r'''"""core_utils.py —— 后台核心工具（祖传代码）"""
import difflib
import re
import time


# 1. 文本差异 ------------------------------------------------------------------
def edit_distance(a, b):
    """把 a 改成 b 最少要插入 / 删除多少行。"""
    a = [line.strip() for line in a]  # 首尾空白不算差异
    b = [line.strip() for line in b]
    if len(a) * len(b) > 4000000:
        # 太大了 DP 跑不动，用 difflib 估一下
        sm = difflib.SequenceMatcher(None, a, b)
        same = sum(block.size for block in sm.get_matching_blocks())
        return len(a) + len(b) - 2 * same
    dp = [[0] * (len(b) + 1) for _ in range(len(a) + 1)]
    for i in range(1, len(a) + 1):
        for j in range(1, len(b) + 1):
            if a[i - 1] == b[j - 1]:
                dp[i][j] = dp[i - 1][j - 1] + 1
            else:
                dp[i][j] = max(dp[i - 1][j], dp[i][j - 1])
    return len(a) + len(b) - 2 * dp[len(a)][len(b)]


# 2. 路径通配 ------------------------------------------------------------------
def _glob_match(p, s):
    if not p:
        return not s
    if p.startswith("**"):
        rest = p[2:].lstrip("/")
        return any(_glob_match(rest, s[i:]) for i in range(len(s) + 1))
    c = p[0]
    if c == "*":
        return any(_glob_match(p[1:], s[i:]) for i in range(len(s) + 1) if "/" not in s[:i])
    if not s:
        return False
    if c == "?":
        return s[0] != "/" and _glob_match(p[1:], s[1:])
    if c == "[":
        end = p.index("]", 2)
        chars = p[1:end]
        if len(chars) == 3 and chars[1] == "-":
            ok = chars[0] <= s[0] <= chars[2]
        else:
            ok = s[0] in chars
        return ok and _glob_match(p[end + 1:], s[1:])
    if c == "\\":
        p = p[1:]
        c = p[0]
    return s[0] == c and _glob_match(p[1:], s[1:])


def glob_filter(pattern, paths):
    """返回 paths 中与通配模式 pattern 匹配的路径。"""
    return [path for path in paths if _glob_match(pattern, path)]


# 3. 撮合引擎 ------------------------------------------------------------------
def _fmt_price(p):
    return ("%.8f" % p).rstrip("0").rstrip(".")


def run_book(commands):
    """按顺序处理委托指令，返回 (事件列表, 盘口快照)。"""
    events = []
    book = {"buy": [], "sell": []}  # 每个元素: [价格, 序号, id, owner, 剩余数量]
    seq = 0
    for cmd in commands:
        op = cmd["op"]
        if op == "cancel":
            for side in ("buy", "sell"):
                for o in book[side]:
                    if o[2] == cmd["id"]:
                        book[side].remove(o)
                        events.append(("cancel", o[2], o[4], "user"))
                        break
                else:
                    continue
                break
            else:
                events.append(("reject", cmd["id"], "unknown_order"))
            continue
        if op == "amend":
            for side in ("buy", "sell"):
                for o in book[side]:
                    if o[2] == cmd["id"]:
                        o[4] = cmd["qty"]
                        events.append(("amend", o[2], cmd["qty"]))
            continue
        side, qty = cmd["side"], cmd["qty"]
        if qty <= 0:
            events.append(("reject", cmd["id"], "bad_qty"))
            continue
        price = float(cmd["price"]) if op == "limit" else None
        opp = "sell" if side == "buy" else "buy"
        while qty > 0 and book[opp]:
            # 每次都重新排序，保证拿到最优价
            if opp == "sell":
                book[opp].sort(key=lambda o: (o[0], o[1]))
            else:
                book[opp].sort(key=lambda o: (-o[0], o[1]))
            best = book[opp][0]
            if price is not None and (best[0] > price if side == "buy" else best[0] < price):
                break
            q = min(qty, best[4])
            qty -= q
            best[4] -= q
            if side == "buy":
                events.append(("trade", cmd["id"], best[2], _fmt_price(best[0]), q))
            else:
                events.append(("trade", best[2], cmd["id"], _fmt_price(best[0]), q))
            if best[4] == 0:
                book[opp].pop(0)
        if qty > 0:
            if op == "limit" and cmd.get("tif", "GTC") == "GTC":
                seq += 1
                book[side].append([price, seq, cmd["id"], cmd.get("owner"), qty])
                events.append(("rest", cmd["id"], _fmt_price(price), qty))
            else:
                events.append(("cancel", cmd["id"], qty, "ioc"))
    snapshot = {}
    for side, name in (("buy", "bids"), ("sell", "asks")):
        levels = {}
        for o in book[side]:
            lv = levels.setdefault(o[0], [0, 0])
            lv[0] += o[4]
            lv[1] += 1
        prices = sorted(levels, reverse=(side == "buy"))
        snapshot[name] = [(_fmt_price(p), levels[p][0], levels[p][1]) for p in prices]
    return events, snapshot


# 4. 缓存 ----------------------------------------------------------------------
class TTLCache:
    """带过期时间、按“大小”限制容量的 LRU 缓存。"""

    def __init__(self, capacity, clock=time.monotonic):
        self.capacity = capacity
        self.clock = clock
        self.data = {}   # key -> (value, size, expire_at)
        self.order = []  # LRU 顺序，最近使用的在末尾
        self.hits = self.misses = self.evictions = self.expirations = 0

    def _used(self):
        return sum(item[1] for item in self.data.values())

    def put(self, key, value, size, ttl):
        if key in self.data:
            self.order.remove(key)
        self.data[key] = (value, size, self.clock() + ttl)
        self.order.append(key)
        while self._used() > self.capacity:
            oldest = self.order.pop(0)
            del self.data[oldest]
            self.evictions += 1

    def get(self, key, default=None):
        if key not in self.data:
            self.misses += 1
            return default
        value, size, expire_at = self.data[key]
        if self.clock() > expire_at:
            del self.data[key]
            self.order.remove(key)
            self.expirations += 1
            self.misses += 1
            return default
        self.order.remove(key)
        self.order.append(key)
        self.hits += 1
        return value

    def delete(self, key):
        if key in self.data:
            del self.data[key]
            self.order.remove(key)
            return True
        return False

    def __len__(self):
        return len(self.data)

    def stats(self):
        return {"hits": self.hits, "misses": self.misses, "evictions": self.evictions,
                "expirations": self.expirations, "size": self._used(), "count": len(self.data)}


# 5. 模板展开 ------------------------------------------------------------------
_REF = re.compile(r"\$\{(\w+)(?::-([^}]*))?\}")


def expand(template, variables, limit):
    """展开模板中的 ${name} 和 ${name:-默认值} 引用。"""
    def repl(m):
        name, default = m.group(1), m.group(2)
        if name in variables:
            return expand(variables[name], variables, limit)
        if default is not None:
            return expand(default, variables, limit)
        return ""  # 找不到就留空
    result = _REF.sub(repl, template.replace("$$", "$"))
    if len(result) > limit:
        raise ValueError("展开结果过长")
    return result
'''

# ════════════════════════════════════════════════════════════════════════════
# 第 2 部分：题目 —— 发给模型的提示词（规格说明）
# ════════════════════════════════════════════════════════════════════════════

PROMPT_TEMPLATE = r"""# 任务：修复并优化 core_utils.py（高难度）

你是一名顶尖的 Python 工程师。下面的 `core_utils.py` 是某交易后台的核心工具模块，包含 4 个函数和 1 个类。这份“祖传代码”能跑，但存在大量问题：功能 bug、安全隐患（拒绝服务等）、并发与资源问题，以及严重的性能问题。

请**重写整个模块**：

1. 每个函数 / 类都必须严格满足下文【规格说明】中的**每一条**规则。规格与现有代码的行为不一致时，以规格为准。
2. 修复所有安全隐患和隐性问题。
3. 在保证正确的前提下尽可能提高性能。评测会在大规模数据和刻意构造的**最坏情况**输入上计时。
4. 只能使用 Python 标准库，兼容 Python 3.8 及以上版本。名称、参数名和参数顺序保持不变；可以新增辅助函数、类、常量和 import。
5. 输出一个**完整的、可以直接保存为 `solution.py` 的 Python 文件**，放在**一个** ```python 代码块中。代码块之后可以简要列出你发现并修复的问题。

## 评分方式

- 每个任务满分 100：功能正确 35 + 安全/隐性问题 35 + 性能 30。隐藏测试包含大量边界条件、恶意输入、最坏情况复杂度测试和多线程测试，并与标准答案做大量随机对拍。
- 性能分以出题人的标准实现为基准：达到标准实现的速度得满 30 分；**比标准实现快 10% 以上开始加分，之后每快一倍再加 10 分，最多 +20 分**。
- 存在安全问题时，该任务性能分为 0；大数据量上的结果不正确时，性能分减半且没有加分；功能测试未全部通过时，性能分按通过比例打折。

## 通用约定

- 不得修改任何传入的参数（包括其中嵌套的列表、字典）。
- 除 `TTLCache` 外，函数结果只取决于本次调用的参数；多次调用之间不能相互影响。
- 规格要求抛出的异常必须是指定的类型（或其子类）。
- 性能测试的大致规模：<<PERF_SCALE>>

## 规格说明

### 1. `edit_distance(a, b) -> int` 文本差异

- `a`、`b` 是字符串列表（文本的各行）。返回把 `a` 变成 `b` 所需的最少操作次数，操作只有两种：删除一行、插入一行（没有“修改”）。也就是 `len(a) + len(b) - 2 × LCS(a, b)`，LCS 为最长公共子序列的长度。
- 行按字符串完全相等比较（大小写、空白字符都要比较）。
- `a`、`b` 各自最多 2 万行。两份文本可能几乎相同，也可能大部分不同（例如被整体重写，或者只由少数几种行反复组成）。**对这个规模内的任意输入，单次调用都必须在约 2 秒内完成**——评测会构造各种最坏情况，并以标准实现的耗时为基准判定是否超时。

### 2. `glob_filter(pattern, paths) -> list[str]` 路径通配

返回 `paths` 中与 `pattern` 匹配的路径，保持原有顺序（重复的路径照常保留）。匹配区分大小写，规则如下：

1. `pattern` 和每个 path 都按 `/` 切分成“段”：`"a//b"` 切成 `["a", "", "b"]`，`"/a"` 切成 `["", "a"]`，`"a/"` 切成 `["a", ""]`，`""` 切成 `[""]`。切分时不考虑转义。
2. 内容恰好是 `**` 的模式段匹配**连续 0 个或多个**路径段，但它匹配的路径段都不能以 `.` 开头（空段可以）。
3. 其它模式段恰好匹配 1 个路径段。段内规则：
   - `*` 匹配任意长度（可以为 0）的任意字符；`?` 匹配恰好 1 个字符；其它字符匹配自身；
   - `\` 使下一个字符成为字面量（在 `[...]` 内也是如此）；
   - `[...]` 匹配集合中的 1 个字符：`!` 或 `^` 紧跟在 `[` 后面表示取反；紧跟在 `[`（或取反符号）后面的 `]` 是字面量；`x-y` 表示码点在 x 到 y 之间（含两端）的字符，起点大于终点的区间不匹配任何字符；`-` 若紧跟在 `]` 之前、或位于集合最开头，则是字面量；集合在第一个不属于上述字面量情况的 `]` 处结束。
4. 以 `.` 开头的路径段，只有当对应模式段的第一个字符是字面量 `.`（写成 `.` 或 `\.`）时才可能匹配；`*`、`?`、`[...]` 都不能匹配路径段开头的 `.`。
5. 任一模式段（`**` 段除外）中出现没有闭合的 `[`、或以未被转义的 `\` 结尾，则模式非法，抛出 `ValueError`——即使 `paths` 为空也要抛出。
6. 规模与复杂度：`pattern` 最长 2000 个字符，单个 path 最长 1 万个字符，`paths` 可能有 10 万条。匹配必须是多项式时间（不允许指数级回溯）；对任意输入，单个 path 的匹配耗时不能超过 O(len(pattern) × len(path)) 的量级。

### 3. `run_book(commands) -> tuple[list[tuple], dict]` 撮合引擎

按顺序处理 `commands` 中的每条指令（dict），返回 `(events, snapshot)`。`id`、`owner` 字段总是字符串。

**指令格式**

- 限价单：`{"op": "limit", "id", "owner", "side": "buy"|"sell", "price": str, "qty": int, "tif": "GTC"|"IOC"|"FOK"}`
- 市价单：`{"op": "market", "id", "owner", "side": "buy"|"sell", "qty": int}`（其它字段忽略）
- 撤单：`{"op": "cancel", "id"}`
- 改量：`{"op": "amend", "id", "qty": int}`（`qty` 为新的剩余数量）

**校验**（不通过时产生 `("reject", id, 原因)` 事件，该指令不产生其它任何效果）。limit / market 按以下顺序检查，命中第一条即拒绝：

1. `op` 不是上述四种之一 → `"bad_order"`；`side` 不是 `"buy"`/`"sell"`，或限价单的 `tif` 不是三者之一 → `"bad_order"`；
2. `qty` 不是 `int`（`bool` 不算 int）或 `<= 0` → `"bad_qty"`；
3. 限价单的 `price` 不是 `str`，或不能完整匹配 `[0-9]+(\.[0-9]{1,8})?`（只允许 ASCII 数字，不允许符号、空白、指数），或数值等于 0 → `"bad_price"`；
4. `id` 与之前任何一条**通过校验**的 limit / market 指令的 `id` 相同（不论那张单现在是否还在簿上）→ `"duplicate_id"`。被拒绝的指令不占用 `id`。

**价格**：价格是精确的十进制数（最多 8 位小数），按数值比较——`"10"`、`"10.0"`、`"010.00"` 是同一个价格。所有输出中的价格都用**规范形式**：去掉整数部分多余的前导零和小数部分末尾的零，小数部分为空时去掉小数点，例如 `"010.50"` → `"10.5"`、`"7.000"` → `"7"`、`"0.10"` → `"0.1"`。

**撮合**（对通过校验的 limit / market 单）：

- 对手方订单按价格优先、时间优先排序：买单与卖一价（最低卖价）开始比较，卖单与买一价（最高买价）开始比较。限价买单只与价格 `<=` 其限价的卖单成交，限价卖单只与价格 `>=` 其限价的买单成交；市价单不限价格。
- 依次取对手方最优的一张订单 r：
  - 若 r 的 `owner` 与新订单相同（自成交），撤掉 r：产生 `("cancel", r.id, r 的剩余数量, "self_trade")`，然后继续；
  - 否则成交 `q = min(新订单剩余, r 剩余)`，**成交价为 r 的价格**，产生 `("trade", 买方 id, 卖方 id, 规范价格, q)`；r 剩余为 0 时从簿上移除（不产生额外事件）。
- 新订单剩余为 0、或没有可成交的对手单时停止。之后：
  - GTC 限价单仍有剩余 → 挂到簿上，产生 `("rest", id, 规范价格, 剩余数量)`；
  - IOC 限价单仍有剩余 → `("cancel", id, 剩余数量, "ioc")`；
  - 市价单仍有剩余 → `("cancel", id, 剩余数量, "no_liquidity")`；
  - 完全成交不产生额外事件。
- FOK 限价单：撮合**之前**先计算所有价格可成交、且 `owner` 与它不同的对手单剩余数量之和。若小于它的 `qty`，产生 `("cancel", id, qty, "fok")`，**不做任何其它改动**（也不触发自成交撤单）；否则按上述规则正常撮合（必然完全成交）。

**撤单**：`id` 是当前挂在簿上的订单 → 移除，产生 `("cancel", id, 剩余数量, "user")`；否则 `("reject", id, "unknown_order")`。

**改量**：`id` 不在簿上 → `("reject", id, "unknown_order")`；否则若 `qty` 不是 `int` 或 `<= 0` → `("reject", id, "bad_qty")`；否则把剩余数量改为 `qty` 并产生 `("amend", id, qty)`：数量减少或不变时保持原有时间优先级；**数量增加时失去时间优先级**，排到同价位的队尾。改量不会触发撮合。

**快照**：`{"bids": [...], "asks": [...]}`，每个价位一项 `(规范价格, 该价位剩余数量之和, 订单数)`；bids 按价格从高到低，asks 按价格从低到高；空价位不出现。

规模：一次调用最多约 20 万条指令，簿上可能同时有数万张订单、数千个价位，撤单可能针对任意位置的订单。

### 4. `class TTLCache` 带过期时间的 LRU 缓存

`TTLCache(capacity, clock)`：`capacity` 是容量（正整数，`bool` 不算），否则抛出 `ValueError`；`clock` 是无参函数，返回当前时间（数值，单调不减）。

- **时钟**：`get`、`put`、`delete`、`__len__`、`stats` 每次调用时**恰好调用 `clock()` 一次**，本次调用中一律使用这个时间 `now`；构造函数不调用 `clock()`；参数校验失败时也不调用。
- **过期**：条目在 `put` 时刻 `now` 加上 `ttl` 得到过期时间 `expire_at`；当 `now >= expire_at` 时该条目视为已过期，不能再被读到。
- `put(key, value, size, ttl)`：`size` 必须是正整数（`bool` 不算），`ttl` 必须是大于 0 的 int 或 float（`bool` 不算），否则抛出 `ValueError`、缓存不变。然后：
  1. 若 key 已存在（不论是否过期），先直接移除旧条目（不计入任何统计）；
  2. 若 `size > capacity`：不存入，直接返回；
  3. 否则作为“最近使用”的条目存入；
  4. 若此时所有条目的 `size` 之和超过 `capacity`：先移除**所有**已过期条目（每个计 1 次 `expirations`），若仍超出，再按“最久未使用”的顺序逐个淘汰（每个计 1 次 `evictions`），直到不超出为止。
- `get(key, default=None)`：命中未过期条目 → 计 1 次 `hits`，把它标记为“最近使用”，返回其值；条目存在但已过期 → 移除它，计 1 次 `expirations` 和 1 次 `misses`，返回 `default`；不存在 → 计 1 次 `misses`，返回 `default`。
- `delete(key)`：存在且未过期 → 移除并返回 `True`；存在但已过期 → 移除，计 1 次 `expirations`，返回 `False`；不存在 → 返回 `False`。
- `__len__()`：先移除所有已过期条目（每个计 1 次 `expirations`），再返回条目数。
- `stats()`：先移除所有已过期条目（同上），再返回 `{"hits", "misses", "evictions", "expirations", "size", "count"}` 六个键的 dict，`size` 为当前所有条目的 `size` 之和，`count` 为条目数。
- 只有 `get` 命中和 `put` 会改变“最近使用”顺序。value 可以是任意对象（包括 None），key 是任意可哈希对象。
- **线程安全**：所有方法都可能被多个线程同时调用，每次调用都必须是原子的。
- **复杂度**：条目可能多达百万个；`get`/`put`/`delete` 必须是（均摊）O(log n) 或更好；`__len__`/`stats` 不能每次都扫描全部条目（均摊到每个被清除的过期条目上 O(log n)）。

### 5. `expand(template, variables, limit) -> str` 模板展开

`variables` 是 `{str: str}`，值本身也是模板。语法：

- `$$` 表示字面量 `$`；`$` 后面跟的既不是 `$` 也不是 `{` 时，这个 `$` 是字面量；
- `${name}` 引用变量，`name` 必须完整匹配 `[A-Za-z_][A-Za-z0-9_]*`（只允许 ASCII）；
- `${name:-default}` 在 `name` 不在 `variables` 中时展开 `default`；`default` 本身也是模板（可以嵌套引用），它从 `:-` 之后开始，到第一个不属于其内部嵌套引用的 `}` 为止；`default` 内部同样适用 `$$` 规则；
- 不在任何 `${...:-` 内部的 `}` 是字面量；
- 其它情况（`${` 后面不是合法变量名，或变量名后面既不是 `}` 也不是 `:-`，或 `${` 没有闭合）都是语法错误。

展开规则与错误（错误一律抛出 `ValueError`）：

- 变量的值按模板递归展开；引用了不在 `variables` 中且没有 `default` 的变量 → 错误；变量之间循环引用（展开 a 的过程中又需要展开 a）→ 错误。
- **惰性**：只解析和展开真正用到的东西。`variables` 中没被用到的值即使有语法错误或循环引用也不影响结果；变量存在时它的 `default` 不会被展开（但 `template` 本身——包括其中所有 `default` 部分——必须整体语法正确）。
- 展开结果的长度超过 `limit` → 错误。
- **规模与安全**：变量之间的引用链、`default` 的嵌套都可能深达 10 万层（不能因递归过深而崩溃；评测这类用例时递归上限会被锁定在几千层，调高 `sys.setrecursionlimit` 无效）；同一个变量可能被引用极多次；恶意输入可能让展开结果的长度呈指数级增长（例如“十亿笑声”攻击）。实现的时间和内存必须与“输入总长度 + min(实际结果长度, limit)”成比例：在确定结果会超过 `limit` 时必须尽早失败，任何时候都不能构造出长度远超 `limit` 的中间字符串。

## 原代码（core_utils.py）

```python
<<CODE>>
```
"""

PERF_SCALE_TEXT = (
    "edit_distance 约 1900 行 vs 1900 行；glob_filter 约 2 万条路径 × 4 个模式；"
    "run_book 约 1.2 万条指令；TTLCache 约 6 万次操作；expand 的引用关系是 11 层的 DAG、顶层被引用数百次。"
    "另有针对最坏情况的大规模计时测试（见各题规格中的规模说明）。"
)


def build_prompt():
    return (PROMPT_TEMPLATE.replace("<<PERF_SCALE>>", PERF_SCALE_TEXT)
            .replace("<<CODE>>", CHALLENGE_CODE.strip("\n")))
# ════════════════════════════════════════════════════════════════════════════
# 第 3 部分：参考答案（判卷用的标准答案，同时作为性能基准）
# ════════════════════════════════════════════════════════════════════════════

# ---------- T1 edit_distance：去掉公共前后缀 + 位并行 LCS（Hyyrö 2004） ----------

_popcount = int.bit_count if hasattr(int, "bit_count") else (lambda x: bin(x).count("1"))


def _ref_edit_distance(a, b):
    n, m = len(a), len(b)
    lo, lim = 0, min(n, m)
    while lo < lim and a[lo] == b[lo]:
        lo += 1
    hi = 0
    while hi < lim - lo and a[n - 1 - hi] == b[m - 1 - hi]:
        hi += 1
    x, y = a[lo:n - hi], b[lo:m - hi]
    if not x or not y:
        return len(x) + len(y)
    if len(x) < len(y):
        x, y = y, x  # 位向量覆盖较长的一侧，逐行扫描较短的一侧
    masks = {}
    get = masks.get
    for i, line in enumerate(x):
        masks[line] = get(line, 0) | (1 << i)
    full = (1 << len(x)) - 1
    v = full
    for line in y:
        mk = get(line)
        if mk is not None:
            u = v & mk
            v = ((v + u) | (v - u)) & full
    lcs = len(x) - _popcount(v)
    return n + m - 2 * (lo + hi + lcs)


# ---------- T2 glob_filter：段内贪心（只用无量词的定长正则）+ 段间位集合 ----------

def _glob_parse_seg(seg):
    """把一个模式段解析成原子：('c', ch) / ('?',) / ('[', ((lo, hi), ...), neg) / ('*',)。"""
    atoms = []
    i, n = 0, len(seg)
    while i < n:
        ch = seg[i]
        if ch == "\\":
            if i + 1 >= n:
                raise ValueError("pattern ends with an unescaped backslash")
            atoms.append(("c", seg[i + 1]))
            i += 2
        elif ch == "*":
            if not atoms or atoms[-1][0] != "*":
                atoms.append(("*",))
            i += 1
        elif ch == "?":
            atoms.append(("?",))
            i += 1
        elif ch == "[":
            j = i + 1
            neg = j < n and seg[j] in "!^"
            if neg:
                j += 1
            items, first = [], True
            while True:
                if j >= n:
                    raise ValueError("unterminated [")
                c = seg[j]
                if c == "]" and not first:
                    j += 1
                    break
                first = False
                if c == "\\":
                    if j + 1 >= n:
                        raise ValueError("unterminated [")
                    c = seg[j + 1]
                    j += 2
                else:
                    j += 1
                if j + 1 < n and seg[j] == "-" and seg[j + 1] != "]":
                    d = seg[j + 1]
                    j += 2
                    if d == "\\":
                        if j >= n:
                            raise ValueError("unterminated [")
                        d = seg[j]
                        j += 1
                    items.append((c, d))
                else:
                    items.append((c, c))
            atoms.append(("[", tuple(items), neg))
            i = j
        else:
            atoms.append(("c", ch))
            i += 1
    return atoms


def _glob_class_re(items, neg):
    def esc(ch):
        return "\\" + ch if ch in "\\]^-[" else ch
    body = "".join(esc(lo) if lo == hi else esc(lo) + "-" + esc(hi) for lo, hi in items if lo <= hi)
    if not body:
        return "." if neg else "(?!)"
    return "[%s%s]" % ("^" if neg else "", body)


def _glob_chunk_re(chunk):
    out = []
    for a in chunk:
        if a[0] == "c":
            out.append(re.escape(a[1]))
        elif a[0] == "?":
            out.append(".")
        else:
            out.append(_glob_class_re(a[1], a[2]))
    return re.compile("".join(out), re.DOTALL)


def _glob_compile_seg(seg):
    atoms = _glob_parse_seg(seg)
    dot_ok = bool(atoms) and atoms[0] == ("c", ".")
    if all(a[0] == "c" for a in atoms):
        lit = "".join(a[1] for a in atoms)
        return lit.__eq__
    chunks = [[]]
    for a in atoms:
        if a[0] == "*":
            chunks.append([])
        else:
            chunks[-1].append(a)
    if len(chunks) == 1:  # 没有 *：定长整段匹配
        rx, ln = _glob_chunk_re(chunks[0]), len(chunks[0])

        def match_fixed(s):
            if len(s) != ln or (not dot_ok and s[:1] == "."):
                return False
            return rx.match(s) is not None
        return match_fixed
    head, tail, mids = chunks[0], chunks[-1], chunks[1:-1]
    rh = _glob_chunk_re(head) if head else None
    rt = _glob_chunk_re(tail) if tail else None
    rms = [_glob_chunk_re(c) for c in mids if c]
    lh, lt = len(head), len(tail)
    need = lh + lt + sum(len(c) for c in mids)

    def match_star(s):
        n = len(s)
        if n < need or (not dot_ok and s[:1] == "."):
            return False
        if rh is not None and rh.match(s) is None:
            return False
        end = n - lt
        if rt is not None and rt.match(s, end) is None:
            return False
        pos = lh
        for r in rms:  # 贪心：每块取最左边的出现位置
            m = r.search(s, pos, end)
            if m is None:
                return False
            pos = m.end()
        return True
    return match_star


def _glob_compile(pattern):
    prog = []
    for seg in pattern.split("/"):
        if seg == "**":
            if not prog or prog[-1] is not None:
                prog.append(None)
        else:
            prog.append(_glob_compile_seg(seg))
    return prog


def _glob_match(prog, path):
    parts = path.split("/")
    reach = 1  # 第 i 位为 1：已匹配完前 i 个路径段
    nodot = -1
    for m in prog:
        if m is None:
            if nodot < 0:
                nodot = 0
                for i, p in enumerate(parts):
                    if p[:1] != ".":
                        nodot |= 1 << i
            reach |= ((reach & nodot) + nodot) ^ nodot
        else:
            nxt, r, size = 0, reach, len(parts)
            while r:
                low = r & -r
                i = low.bit_length() - 1
                if i < size and m(parts[i]):
                    nxt |= low << 1
                r ^= low
            reach = nxt
            if not reach:
                return False
    return (reach >> len(parts)) & 1 == 1


def _ref_glob_filter(pattern, paths):
    prog = _glob_compile(pattern)
    return [p for p in paths if _glob_match(prog, p)]


# ---------- T3 run_book：整数化价格 + 有序价位列表 + 每价位 OrderedDict ----------

_BOOK_SCALE = 10 ** 8
_BOOK_PRICE_RE = re.compile(r"[0-9]+(?:\.[0-9]{1,8})?")


def _book_price(s):
    if type(s) is not str or _BOOK_PRICE_RE.fullmatch(s) is None:
        return None
    whole, _, frac = s.partition(".")
    v = int(whole) * _BOOK_SCALE + (int(frac.ljust(8, "0")) if frac else 0)
    return v if v > 0 else None


def _book_fmt(v):
    whole, frac = divmod(v, _BOOK_SCALE)
    return str(whole) if not frac else "%d.%s" % (whole, ("%08d" % frac).rstrip("0"))


class _BookOrder(object):
    __slots__ = ("owner", "side", "key", "qty")


def _ref_run_book(commands):
    events = []
    emit = events.append
    used = set()
    resting = {}
    levels = ({}, {})   # 0=买 1=卖；key -> OrderedDict(id -> 订单)；key 买方为价格，卖方为 -价格
    keys = ([], [])     # 升序 key 列表，最优价位在末尾

    def drop_level(side, key):
        del levels[side][key]
        ks = keys[side]
        del ks[bisect.bisect_left(ks, key)]

    for cmd in commands:
        op = cmd.get("op")
        oid = cmd.get("id")
        if op == "cancel":
            o = resting.pop(oid, None)
            if o is None:
                emit(("reject", oid, "unknown_order"))
                continue
            q = levels[o.side][o.key]
            del q[oid]
            if not q:
                drop_level(o.side, o.key)
            emit(("cancel", oid, o.qty, "user"))
            continue
        if op == "amend":
            o = resting.get(oid)
            if o is None:
                emit(("reject", oid, "unknown_order"))
                continue
            qty = cmd.get("qty")
            if type(qty) is not int or qty <= 0:
                emit(("reject", oid, "bad_qty"))
                continue
            if qty > o.qty:
                levels[o.side][o.key].move_to_end(oid)
            o.qty = qty
            emit(("amend", oid, qty))
            continue
        if op not in ("limit", "market"):
            emit(("reject", oid, "bad_order"))
            continue
        side_name, tif = cmd.get("side"), cmd.get("tif")
        if side_name not in ("buy", "sell") or (op == "limit" and tif not in ("GTC", "IOC", "FOK")):
            emit(("reject", oid, "bad_order"))
            continue
        qty = cmd.get("qty")
        if type(qty) is not int or qty <= 0:
            emit(("reject", oid, "bad_qty"))
            continue
        price = None
        if op == "limit":
            price = _book_price(cmd.get("price"))
            if price is None:
                emit(("reject", oid, "bad_price"))
                continue
        else:
            tif = None
        if oid in used:
            emit(("reject", oid, "duplicate_id"))
            continue
        used.add(oid)
        owner = cmd.get("owner")
        side = 0 if side_name == "buy" else 1
        opp = 1 - side
        oks, olv = keys[opp], levels[opp]
        if tif == "FOK":
            need = qty
            for k in reversed(oks):
                p = k if opp == 0 else -k
                if price is not None and (p > price if side == 0 else p < price):
                    break
                for r in olv[k].values():
                    if r.owner != owner:
                        need -= r.qty
                        if need <= 0:
                            break
                if need <= 0:
                    break
            if need > 0:
                emit(("cancel", oid, qty, "fok"))
                continue
        remaining = qty
        while remaining and oks:
            k = oks[-1]
            p = k if opp == 0 else -k
            if price is not None and (p > price if side == 0 else p < price):
                break
            q = olv[k]
            rid, r = next(iter(q.items()))
            if r.owner == owner:
                del q[rid]
                del resting[rid]
                emit(("cancel", rid, r.qty, "self_trade"))
            else:
                t = remaining if remaining < r.qty else r.qty
                remaining -= t
                r.qty -= t
                emit(("trade", oid, rid, _book_fmt(p), t) if side == 0 else ("trade", rid, oid, _book_fmt(p), t))
                if not r.qty:
                    del q[rid]
                    del resting[rid]
            if not q:
                del olv[k]
                oks.pop()
        if remaining:
            if op == "market":
                emit(("cancel", oid, remaining, "no_liquidity"))
            elif tif == "IOC":
                emit(("cancel", oid, remaining, "ioc"))
            else:
                o = _BookOrder()
                o.owner, o.side, o.qty = owner, side, remaining
                o.key = price if side == 0 else -price
                q = levels[side].get(o.key)
                if q is None:
                    q = levels[side][o.key] = collections.OrderedDict()
                    bisect.insort(keys[side], o.key)
                q[oid] = o
                resting[oid] = o
                emit(("rest", oid, _book_fmt(price), remaining))
    snapshot = {"bids": [], "asks": []}
    for side, name in ((0, "bids"), (1, "asks")):
        for k in reversed(keys[side]):
            q = levels[side][k]
            snapshot[name].append((_book_fmt(k if side == 0 else -k), sum(o.qty for o in q.values()), len(q)))
    return events, snapshot


# ---------- T4 TTLCache：OrderedDict（LRU）+ 过期时间小顶堆（惰性删除）+ 锁 ----------

class _RefTTLCache(object):
    def __init__(self, capacity, clock):
        if type(capacity) is not int or capacity <= 0:
            raise ValueError("capacity must be a positive int")
        self._capacity = capacity
        self._clock = clock
        self._lock = threading.Lock()
        self._data = collections.OrderedDict()  # key -> [value, size, expire_at, seq]
        self._heap = []                         # (expire_at, seq, key)
        self._seq = 0
        self._size = 0
        self._hits = self._misses = self._evictions = self._expirations = 0

    def _purge(self, now):
        heap, data = self._heap, self._data
        while heap and heap[0][0] <= now:
            _, seq, key = heapq.heappop(heap)
            item = data.get(key)
            if item is not None and item[3] == seq:
                del data[key]
                self._size -= item[1]
                self._expirations += 1

    def _compact(self):
        if len(self._heap) > 64 and len(self._heap) > 2 * len(self._data):
            self._heap = [(it[2], it[3], k) for k, it in self._data.items()]
            heapq.heapify(self._heap)

    def put(self, key, value, size, ttl):
        if type(size) is not int or size <= 0:
            raise ValueError("size must be a positive int")
        if type(ttl) not in (int, float) or not ttl > 0:
            raise ValueError("ttl must be a positive number")
        with self._lock:
            now = self._clock()
            data = self._data
            old = data.pop(key, None)
            if old is not None:
                self._size -= old[1]
            if size > self._capacity:
                return
            self._seq += 1
            expire = now + ttl
            data[key] = [value, size, expire, self._seq]
            heapq.heappush(self._heap, (expire, self._seq, key))
            self._size += size
            if self._size > self._capacity:
                self._purge(now)
                while self._size > self._capacity:
                    _, item = data.popitem(last=False)
                    self._size -= item[1]
                    self._evictions += 1
            self._compact()

    def get(self, key, default=None):
        with self._lock:
            now = self._clock()
            item = self._data.get(key)
            if item is None:
                self._misses += 1
                return default
            if now >= item[2]:
                del self._data[key]
                self._size -= item[1]
                self._expirations += 1
                self._misses += 1
                return default
            self._data.move_to_end(key)
            self._hits += 1
            return item[0]

    def delete(self, key):
        with self._lock:
            now = self._clock()
            item = self._data.pop(key, None)
            if item is None:
                return False
            self._size -= item[1]
            if now >= item[2]:
                self._expirations += 1
                return False
            return True

    def __len__(self):
        with self._lock:
            self._purge(self._clock())
            self._compact()
            return len(self._data)

    def stats(self):
        with self._lock:
            self._purge(self._clock())
            self._compact()
            return {"hits": self._hits, "misses": self._misses, "evictions": self._evictions,
                    "expirations": self._expirations, "size": self._size, "count": len(self._data)}


# ---------- T5 expand：迭代解析 + 迭代展开（显式栈）+ 变量结果缓存 + 增量长度检查 ----------

_TPL_NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")
_TPL_TEXT_TOP = re.compile(r"[^$]+")
_TPL_TEXT_IN = re.compile(r"[^$}]+")


def _tpl_parse(text):
    """解析成片段列表：str 为字面量，(name, default) 为引用；default 为 None 或片段列表。"""
    root = out = []
    stack = []
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if c == "$":
            nxt = text[i + 1:i + 2]
            if nxt == "$":
                out.append("$")
                i += 2
            elif nxt == "{":
                m = _TPL_NAME.match(text, i + 2)
                if m is None:
                    raise ValueError("bad reference at offset %d" % i)
                j = m.end()
                if text.startswith("}", j):
                    out.append((m.group(), None))
                    i = j + 1
                elif text.startswith(":-", j):
                    stack.append((out, m.group()))
                    out = []
                    i = j + 2
                else:
                    raise ValueError("bad reference at offset %d" % i)
            else:
                out.append("$")
                i += 1
        elif c == "}" and stack:
            parent, name = stack.pop()
            parent.append((name, out))
            out = parent
            i += 1
        else:
            m = (_TPL_TEXT_IN if stack else _TPL_TEXT_TOP).match(text, i)
            out.append(m.group())
            i = m.end()
    if stack:
        raise ValueError("unterminated ${")
    return root


def _ref_expand(template, variables, limit):
    parsed, memo, active = {}, {}, set()
    stack = [[_tpl_parse(template), 0, [], 0, None]]  # [片段, 下标, 已生成的片段, 已生成长度, 变量名]
    while True:
        f = stack[-1]
        parts = f[0]
        if f[1] == len(parts):
            s = "".join(f[2])
            stack.pop()
            if f[4] is not None:
                memo[f[4]] = s
                active.discard(f[4])
            if not stack:
                return s
            g = stack[-1]
            g[3] += len(s)
            if g[3] > limit:
                raise ValueError("expansion exceeds limit")
            g[2].append(s)
            continue
        part = parts[f[1]]
        f[1] += 1
        if part.__class__ is str:
            f[3] += len(part)
            if f[3] > limit:
                raise ValueError("expansion exceeds limit")
            f[2].append(part)
            continue
        name, default = part
        if name in variables:
            s = memo.get(name)
            if s is not None:
                f[3] += len(s)
                if f[3] > limit:
                    raise ValueError("expansion exceeds limit")
                f[2].append(s)
                continue
            if name in active:
                raise ValueError("reference cycle at %r" % name)
            p = parsed.get(name)
            if p is None:
                p = parsed[name] = _tpl_parse(variables[name])
            active.add(name)
            stack.append([p, 0, [], 0, name])
        elif default is not None:
            stack.append([default, 0, [], 0, None])
        else:
            raise ValueError("undefined variable %r" % name)


REFERENCE = {
    "edit_distance": _ref_edit_distance,
    "glob_filter": _ref_glob_filter,
    "run_book": _ref_run_book,
    "TTLCache": _RefTTLCache,
    "expand": _ref_expand,
}
# ════════════════════════════════════════════════════════════════════════════
# 第 4 部分：独立的朴素实现（只用于自检：与参考答案随机对拍，验证标准答案本身）
# ════════════════════════════════════════════════════════════════════════════

def _naive_edit_distance(a, b):
    prev = [0] * (len(b) + 1)
    for x in a:
        cur = [0]
        for j, y in enumerate(b):
            cur.append(prev[j] + 1 if x == y else max(prev[j + 1], cur[j]))
        prev = cur
    return len(a) + len(b) - 2 * prev[-1]


def _naive_class(p, i, ch):
    """p[i] == '['；返回 (ch 是否匹配, 类结束后的下标)。"""
    j = i + 1
    neg = p[j:j + 1] in ("!", "^")
    if neg:
        j += 1
    toks, first = [], True
    while True:
        if j >= len(p):
            raise ValueError("unterminated [")
        c = p[j]
        if c == "]" and not first:
            j += 1
            break
        first = False
        if c == "\\":
            if j + 1 >= len(p):
                raise ValueError("unterminated [")
            toks.append(("lit", p[j + 1]))
            j += 2
        elif c == "-":
            toks.append(("dash", "-"))
            j += 1
        else:
            toks.append(("lit", c))
            j += 1
    hit, k = False, 0
    while k < len(toks):
        if k + 2 < len(toks) and toks[k + 1][0] == "dash":
            if toks[k][1] <= ch <= toks[k + 2][1]:
                hit = True
            k += 3
        else:
            if toks[k][1] == ch:
                hit = True
            k += 1
    return hit != neg, j


def _naive_validate_seg(p):
    i = 0
    while i < len(p):
        if p[i] == "\\":
            if i + 1 >= len(p):
                raise ValueError("trailing backslash")
            i += 2
        elif p[i] == "[":
            i = _naive_class(p, i, "x")[1]
        else:
            i += 1


@functools.lru_cache(maxsize=None)
def _naive_chars(p, i, s, j):
    if i == len(p):
        return j == len(s)
    c = p[i]
    if c == "*":
        return any(_naive_chars(p, i + 1, s, k) for k in range(j, len(s) + 1))
    if j == len(s):
        return False
    if c == "?":
        return _naive_chars(p, i + 1, s, j + 1)
    if c == "\\":
        return p[i + 1] == s[j] and _naive_chars(p, i + 2, s, j + 1)
    if c == "[":
        ok, end = _naive_class(p, i, s[j])
        return ok and _naive_chars(p, end, s, j + 1)
    return c == s[j] and _naive_chars(p, i + 1, s, j + 1)


@functools.lru_cache(maxsize=None)
def _naive_segs(ps, ss):
    if not ps:
        return not ss
    if ps[0] == "**":
        for k in range(len(ss) + 1):
            if k and ss[k - 1].startswith("."):
                break
            if _naive_segs(ps[1:], ss[k:]):
                return True
        return False
    if not ss:
        return False
    p, s = ps[0], ss[0]
    if s.startswith(".") and not (p.startswith(".") or p.startswith("\\.")):
        return False
    return _naive_chars(p, 0, s, 0) and _naive_segs(ps[1:], ss[1:])


def _naive_glob_filter(pattern, paths):
    ps = tuple(pattern.split("/"))
    for seg in ps:
        if seg != "**":
            _naive_validate_seg(seg)
    return [x for x in paths if _naive_segs(ps, tuple(x.split("/")))]


def _naive_run_book(commands):
    from decimal import Decimal
    events, used, book = [], set(), []
    seq = [0]

    def fmt(d):
        s = format(d, "f")
        return s.rstrip("0").rstrip(".") if "." in s else s

    def find(oid):
        for o in book:
            if o["id"] == oid:
                return o
        return None

    def ok_price(s):
        return type(s) is str and re.fullmatch(r"[0-9]+(\.[0-9]{1,8})?", s) is not None and Decimal(s) > 0

    for cmd in commands:
        op, oid = cmd.get("op"), cmd.get("id")
        if op == "cancel":
            o = find(oid)
            if o is None:
                events.append(("reject", oid, "unknown_order"))
            else:
                book.remove(o)
                events.append(("cancel", oid, o["qty"], "user"))
            continue
        if op == "amend":
            o, qty = find(oid), cmd.get("qty")
            if o is None:
                events.append(("reject", oid, "unknown_order"))
            elif type(qty) is not int or qty <= 0:
                events.append(("reject", oid, "bad_qty"))
            else:
                if qty > o["qty"]:
                    seq[0] += 1
                    o["seq"] = seq[0]
                o["qty"] = qty
                events.append(("amend", oid, qty))
            continue
        if op not in ("limit", "market") or cmd.get("side") not in ("buy", "sell") or \
                (op == "limit" and cmd.get("tif") not in ("GTC", "IOC", "FOK")):
            events.append(("reject", oid, "bad_order"))
            continue
        qty = cmd.get("qty")
        if type(qty) is not int or qty <= 0:
            events.append(("reject", oid, "bad_qty"))
            continue
        if op == "limit" and not ok_price(cmd.get("price")):
            events.append(("reject", oid, "bad_price"))
            continue
        if oid in used:
            events.append(("reject", oid, "duplicate_id"))
            continue
        used.add(oid)
        side, owner = cmd["side"], cmd.get("owner")
        price = Decimal(cmd["price"]) if op == "limit" else None
        tif = cmd.get("tif") if op == "limit" else None

        def crossing():
            res = [o for o in book if o["side"] != side and
                   (price is None or (o["price"] <= price if side == "buy" else o["price"] >= price))]
            res.sort(key=lambda o: ((o["price"] if side == "buy" else -o["price"]), o["seq"]))
            return res

        if tif == "FOK" and sum(o["qty"] for o in crossing() if o["owner"] != owner) < qty:
            events.append(("cancel", oid, qty, "fok"))
            continue
        left = qty
        while left:
            cs = crossing()
            if not cs:
                break
            r = cs[0]
            if r["owner"] == owner:
                book.remove(r)
                events.append(("cancel", r["id"], r["qty"], "self_trade"))
                continue
            t = min(left, r["qty"])
            left -= t
            r["qty"] -= t
            ids = (oid, r["id"]) if side == "buy" else (r["id"], oid)
            events.append(("trade", ids[0], ids[1], fmt(r["price"]), t))
            if not r["qty"]:
                book.remove(r)
        if left:
            if op == "market":
                events.append(("cancel", oid, left, "no_liquidity"))
            elif tif == "IOC":
                events.append(("cancel", oid, left, "ioc"))
            else:
                seq[0] += 1
                book.append({"id": oid, "owner": owner, "side": side, "price": price, "qty": left, "seq": seq[0]})
                events.append(("rest", oid, fmt(price), left))
    snap = {}
    for side, name in (("buy", "bids"), ("sell", "asks")):
        lv = {}
        for o in book:
            if o["side"] == side:
                e = lv.setdefault(o["price"], [0, 0])
                e[0] += o["qty"]
                e[1] += 1
        snap[name] = [(fmt(p), lv[p][0], lv[p][1]) for p in sorted(lv, reverse=(side == "buy"))]
    return events, snap


class _NaiveTTLCache(object):
    def __init__(self, capacity, clock):
        if type(capacity) is not int or capacity <= 0:
            raise ValueError("capacity")
        self.cap, self.clock = capacity, clock
        self.items, self.order = {}, []
        self.h = self.m = self.ev = self.ex = 0

    def _drop(self, k):
        del self.items[k]
        self.order.remove(k)

    def _purge(self, now):
        for k in [k for k in self.order if now >= self.items[k][2]]:
            self._drop(k)
            self.ex += 1

    def _total(self):
        return sum(v[1] for v in self.items.values())

    def put(self, key, value, size, ttl):
        if type(size) is not int or size <= 0 or type(ttl) not in (int, float) or not ttl > 0:
            raise ValueError("bad args")
        now = self.clock()
        if key in self.items:
            self._drop(key)
        if size > self.cap:
            return
        self.items[key] = (value, size, now + ttl)
        self.order.append(key)
        if self._total() > self.cap:
            self._purge(now)
            while self._total() > self.cap:
                self._drop(self.order[0])
                self.ev += 1

    def get(self, key, default=None):
        now = self.clock()
        if key not in self.items:
            self.m += 1
            return default
        if now >= self.items[key][2]:
            self._drop(key)
            self.ex += 1
            self.m += 1
            return default
        self.order.remove(key)
        self.order.append(key)
        self.h += 1
        return self.items[key][0]

    def delete(self, key):
        now = self.clock()
        if key not in self.items:
            return False
        expired = now >= self.items[key][2]
        self._drop(key)
        if expired:
            self.ex += 1
        return not expired

    def __len__(self):
        self._purge(self.clock())
        return len(self.items)

    def stats(self):
        self._purge(self.clock())
        return {"hits": self.h, "misses": self.m, "evictions": self.ev, "expirations": self.ex,
                "size": self._total(), "count": len(self.items)}


def _naive_tpl_parse(text, i=0, in_default=False):
    parts = []
    while i < len(text):
        if text.startswith("$$", i):
            parts.append("$")
            i += 2
        elif text.startswith("${", i):
            m = re.compile(r"[A-Za-z_][A-Za-z0-9_]*").match(text, i + 2)
            if m is None:
                raise ValueError("bad name")
            j = m.end()
            if text.startswith("}", j):
                parts.append((m.group(), None))
                i = j + 1
            elif text.startswith(":-", j):
                sub, i = _naive_tpl_parse(text, j + 2, True)
                parts.append((m.group(), sub))
            else:
                raise ValueError("bad ref")
        elif in_default and text[i] == "}":
            return parts, i + 1
        else:
            parts.append(text[i])
            i += 1
    if in_default:
        raise ValueError("unterminated")
    return parts, i


def _naive_expand(template, variables, limit):
    memo = {}

    def run(parts, active):
        out = []
        for p in parts:
            if isinstance(p, str):
                out.append(p)
                continue
            name, default = p
            if name in variables:
                if name not in memo:
                    if name in active:
                        raise ValueError("cycle")
                    memo[name] = run(_naive_tpl_parse(variables[name])[0], active | {name})
                out.append(memo[name])
            elif default is not None:
                out.append(run(default, active))
            else:
                raise ValueError("undefined")
        return "".join(out)

    res = run(_naive_tpl_parse(template)[0], frozenset())
    if len(res) > limit:
        raise ValueError("too long")
    return res
# ════════════════════════════════════════════════════════════════════════════
# 第 5 部分：判卷工具函数
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
            if key not in b or not _same(va, b[key]):
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


def _ft(sec):
    if sec is None:
        return "-"
    if sec >= 1:
        return "%.2fs" % sec
    if sec >= 1e-3:
        return "%.1fms" % (sec * 1e3)
    return "%.0fµs" % (sec * 1e6)


def _outcome(fn, args):
    try:
        return ("ok", fn(*args))
    except KeyboardInterrupt:
        raise
    except BaseException as e:  # SystemExit、RecursionError、MemoryError 等也算候选代码的失败
        return ("exc", e)


def _judge_outcome(got, exp):
    kind, val = exp
    if kind == "value":
        if got[0] == "exc":
            return "期望返回 %s，实际抛出 %s" % (_short(val, 120), _fmt_exc(got[1]))
        if not _same(got[1], val):
            if len(repr(val)) > 600:
                d = _first_diff(val, got[1], "结果")
                return "结果不符（输出很长，只显示第一处差异：期望 → 实际）\n        %s" % d
            return "结果不符\n        期望: %s\n        实际: %s" % (_short(val, 300), _short(got[1], 300))
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


def _eval_cases(fn, ref_fn, cases, call=None, limit=4):
    """cases: [(标签, 参数工厂, 期望)]，按顺序逐个调用；期望为 REF 时以参考答案的结果为准。"""
    def run_one(f, args):
        return _outcome(call, (f, args)) if call else _outcome(f, args)
    fails = []
    for label, make_args, exp in cases:
        if exp is REF:
            ro = run_one(ref_fn, make_args())
            exp = _V(ro[1]) if ro[0] == "ok" else _E(type(ro[1]))
        msg = _judge_outcome(run_one(fn, make_args()), exp)
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


class _MissingFunction(Exception):
    pass


def _get_fn(impl, name):
    fn = impl.get(name)
    if fn is None:
        raise _MissingFunction(name)
    return fn


def _cases(fname, cases, call=None):
    def run(impl, ref):
        return _eval_cases(_get_fn(impl, fname), ref[fname], cases, call=call)
    return run


def _no_mutation(fname, make_args, arg_names, call=None):
    def run(impl, ref):
        fn = _get_fn(impl, fname)
        args = make_args()
        snapshot = copy.deepcopy(args)
        got = _outcome(call, (fn, args)) if call else _outcome(fn, args)
        if got[0] == "exc":
            return "fail", "调用抛出异常，无法完成检查: " + _fmt_exc(got[1])
        for name, before, after in zip(arg_names, snapshot, args):
            d = _first_diff(before, after, name)
            if d:
                return "fail", "入参被修改: " + d
        return "pass", ""
    return run


def _random_cases(gen, n, seed, show=200):
    rng = random.Random(seed)
    out = []
    for i in range(n):
        args = gen(rng)
        out.append(("随机#%d 输入=%s" % (i + 1, _short(args, show)), _const(*args), REF))
    return out


def _timed_case(fname, make_args, factor, floor=0.25, call=None):
    """最坏情况计时测试：先在同一进程里计时标准实现，候选结果必须正确，且耗时不超过 max(floor, factor × 标准耗时)。"""
    call = call or (lambda f, args: f(*args))

    def run(impl, ref):
        fn = _get_fn(impl, fname)
        args = make_args()
        gc.collect()
        t0 = time.perf_counter()
        ro = _outcome(call, (ref[fname], args))
        t_ref = time.perf_counter() - t0
        exp = _V(ro[1]) if ro[0] == "ok" else _E(type(ro[1]))
        del args, ro
        args = make_args()
        gc.collect()
        t0 = time.perf_counter()
        got = _outcome(call, (fn, args))
        t_c = time.perf_counter() - t0
        msg = _judge_outcome(got, exp)
        cap = max(floor, factor * t_ref)
        if t_c > cap:
            return "fail", "耗时 %s，超过上限 %s（标准实现 %s 的 %g 倍）%s" % (
                _ft(t_c), _ft(cap), _ft(t_ref), factor, "；另外结果也不正确: " + msg if msg else "")
        if got[0] == "exc" and not isinstance(got[1], ValueError):
            return "fail", msg  # 崩溃（RecursionError、MemoryError 等）不算“复杂度达标”
        if msg:
            return "partial", "复杂度达标（耗时 %s，上限 %s），但结果与标准答案不一致（得一半分）: %s" % (_ft(t_c), _ft(cap), msg)
        return "pass", "耗时 %s（标准实现 %s，上限 %s）" % (_ft(t_c), _ft(t_ref), _ft(cap))
    return run


class Test:
    def __init__(self, cat, desc, run, weight=1):
        self.cat, self.desc, self.run, self.weight = cat, desc, run, weight
        self.id = ""


# ════════════════════════════════════════════════════════════════════════════
# 第 6 部分：各任务的隐藏测试
# ════════════════════════════════════════════════════════════════════════════

# ---------- T1 edit_distance ----------

def _rand_t1(rng):
    alphabet = rng.choice(["ab", "abc", "abcdefgh", "xyz "])
    alphabet = list(alphabet) + ["a ", " a", "A"]
    return ([rng.choice(alphabet) for _ in range(rng.randint(0, 30))],
            [rng.choice(alphabet) for _ in range(rng.randint(0, 30))])


def _t1_unique_lines(rng, n, tag):
    return ["%s line %d: %08x" % (tag, i, rng.getrandbits(32)) for i in range(n)]


def _t1_mutate(rng, lines, k):
    out = list(lines)
    for _ in range(k):
        r = rng.random()
        pos = rng.randrange(len(out) + 1)
        if r < 0.4 and out:
            del out[min(pos, len(out) - 1)]
        elif r < 0.8:
            out.insert(pos, "inserted %08x" % rng.getrandbits(32))
        elif out:
            out[min(pos, len(out) - 1)] = "changed %08x" % rng.getrandbits(32)
    out[0] = "changed head"
    out[-1] = "changed tail"
    return out


def _t1_big_similar():
    rng = random.Random(11)
    a = _t1_unique_lines(rng, 20000, "f")
    return a, _t1_mutate(rng, a, 40)


def _t1_big_repetitive():
    rng = random.Random(12)
    vocab = ["    return x", "}", "", "{", "    pass", "x = 1", "# comment"] + ["tok%d" % i for i in range(23)]
    return [rng.choice(vocab) for _ in range(20000)], [rng.choice(vocab) for _ in range(20000)]


def _t1_big_disjoint():
    rng = random.Random(13)
    return _t1_unique_lines(rng, 20000, "left"), _t1_unique_lines(rng, 20000, "right")


def _t1_big_skewed():
    rng = random.Random(14)
    a = _t1_unique_lines(rng, 20000, "s")
    return a, [a[i] if i % 3 else "other %d" % i for i in range(0, 20000, 67)]


def _t1_medium():
    rng = random.Random(15)
    vocab = ["l%d" % i for i in range(200)] + [""] * 30 + ["}"] * 30
    a = [rng.choice(vocab) for _ in range(2500)]
    b = list(a)
    for _ in range(300):
        i = rng.randrange(len(b))
        b[i] = rng.choice(vocab)
    return a, b


def _tests_t1():
    F = "edit_distance"
    big = lambda gen: (lambda: gen())  # noqa: E731
    return [
        Test("功能", "基本示例", _cases(F, [
            _c("abc→acd", _V(2), ["a", "b", "c"], ["a", "c", "d"]),
            _c("相同", _V(0), ["a", "a", "a"], ["a", "a", "a"]),
            _c("空→2 行", _V(2), [], ["x", "y"]),
            _c("1 行→空", _V(1), ["x"], []),
            _c("空→空", _V(0), [], []),
        ])),
        Test("功能", "行按完全相等比较（空白、大小写都算）", _cases(F, [
            _c("尾随空格/大小写", _V(4), ["a ", "B"], ["a", "b"]),
            _c("制表符", _V(2), ["\tx"], ["x"]),
            _c("空行", _V(1), ["", ""], [""]),
        ])),
        Test("功能", "大量重复行", _cases(F, [
            _c("ababa→bab", _V(2), ["a", "b", "a", "b", "a"], ["b", "a", "b"]),
            _c("交错", _V(2), ["a", "b"] * 4, ["b", "a"] * 3),
        ])),
        Test("功能", "随机对拍（80 组）", _cases(F, _random_cases(_rand_t1, 80, 101)), weight=3),
        Test("功能", "中等规模（2500 行、重复行多）结果必须是最少操作数", _cases(F, [
            ("2500×2500", big(_t1_medium), REF),
        ])),
        # 上限约为“2 秒（在标准实现耗时 ~50ms 的机器上）”：factor ≈ 2s / 标准实现耗时，随机器快慢等比缩放
        Test("隐性", "复杂度：2 万行、少量分散修改（首尾也改了）",
             _timed_case(F, big(_t1_big_similar), factor=35)),
        Test("隐性", "复杂度：2 万行、只由 30 种行组成且差异巨大",
             _timed_case(F, big(_t1_big_repetitive), factor=40)),
        Test("隐性", "复杂度：2 万行 vs 2 万行、完全不同",
             _timed_case(F, big(_t1_big_disjoint), factor=150)),
        Test("隐性", "复杂度：2 万行 vs 300 行",
             _timed_case(F, big(_t1_big_skewed), factor=180)),
        Test("隐性", "不修改入参", _no_mutation(F, _const(["b", "a", "c"], ["c", "a"]), ("a", "b"))),
    ]


# ---------- T2 glob_filter ----------

def _rand_t2(rng):
    atoms = ["a", "b", ".", "*", "?", "[ab]", "[!a]", "[^b]", "[]a]", "[a-]", "[-b]", "[b-a]", "\\*", "\\.",
             "[\\]]", "x", "-", "**"]
    if rng.random() < 0.08:
        atoms = atoms + ["[", "\\"]
    segs = []
    for _ in range(rng.randint(1, 4)):
        segs.append("**" if rng.random() < 0.2 else "".join(rng.choice(atoms) for _ in range(rng.randint(0, 4))))
    paths = ["/".join("".join(rng.choice("ab.x*]-") for _ in range(rng.randint(0, 3)))
                      for _ in range(rng.randint(1, 4))) for _ in range(rng.randint(0, 8))]
    return ("/".join(segs), paths)


def _gc(pattern, paths, expected):
    exp = expected if isinstance(expected, tuple) else _V(expected)
    return _c(repr(pattern), exp, pattern, paths)


def _t2_throughput():
    rng = random.Random(21)
    dirs = ["src", "lib", "tests", "docs", ".git", "build", "vendor", "pkg"]
    paths = []
    for _ in range(100000):
        depth = rng.randint(1, 6)
        segs = [rng.choice(dirs) if rng.random() < 0.5 else "m%d" % rng.randrange(500) for _ in range(depth)]
        segs.append(rng.choice(["test_%d.py", "main_%d.c", "util%d.h", ".hidden%d", "README_%d.md"]) % rng.randrange(100))
        paths.append("/".join(segs))
    return ("**/[!._]*_[0-9]*.[ch]", paths)


def _tests_t2():
    F = "glob_filter"
    VE = _E(ValueError)
    return [
        Test("功能", "字面量、* 与 ?（* 和 ? 不跨越 /）", _cases(F, [
            _gc("src/*.py", ["src/a.py", "src/b/c.py", "src/a.pyc", "src/py", "SRC/a.py", "src/.py.py"], ["src/a.py"]),
            _gc("?.txt", ["a.txt", "ab.txt", "/.txt", ".txt"], ["a.txt"]),
            _gc("a*b*c", ["abc", "aXbYc", "ab/c", "acb", "abcbc"], ["abc", "aXbYc", "abcbc"]),
        ])),
        Test("功能", "字符集合：区间 / 取反 / 开头的 ] 与 - / 末尾的 - / 反向区间", _cases(F, [
            _gc("[a-c]x", ["ax", "bx", "dx", "Ax"], ["ax", "bx"]),
            _gc("[!a-c]x", ["ax", "dx", "-x"], ["dx", "-x"]),
            _gc("[^0-9]", ["5", "x"], ["x"]),
            _gc("[]a]", ["]", "a", "b"], ["]", "a"]),
            _gc("[!]a]", ["]", "a", "b"], ["b"]),
            _gc("[a-]", ["a", "-", "b"], ["a", "-"]),
            _gc("[-z]", ["-", "z", "m"], ["-", "z"]),
            _gc("[z-a]", ["z", "a", "m"], []),
            _gc("[!z-a]", ["m", "z"], ["m", "z"]),
            _gc("[α-ω]x", ["βx", "ax", "Ωx"], ["βx"]),
        ])),
        Test("功能", "转义（包括集合内的转义）", _cases(F, [
            _gc("\\*", ["*", "a"], ["*"]),
            _gc("a\\?b", ["a?b", "axb"], ["a?b"]),
            _gc("[\\]]", ["]", "\\"], ["]"]),
            _gc("\\[a]", ["[a]", "a"], ["[a]"]),
            _gc("[\\-a]", ["-", "a", "b", "\\"], ["-", "a"]),
            _gc("\\\\", ["\\", "\\\\"], ["\\"]),
            _gc("[\\!a]", ["!", "a", "b"], ["!", "a"]),
        ])),
        Test("功能", "** 段匹配 0 个或多个整段；段内的 ** 等同于 *", _cases(F, [
            _gc("a/**/b", ["a/b", "a/x/b", "a/x/y/b", "a/xb", "ab", "a/b/c"], ["a/b", "a/x/b", "a/x/y/b"]),
            _gc("**/b", ["b", "x/b", "x/y/b", "xb", "b/x"], ["b", "x/b", "x/y/b"]),
            _gc("a/**", ["a", "a/x", "a/x/y", "ab", "b/a"], ["a", "a/x", "a/x/y"]),
            _gc("**", ["", "a", "a/b/c", "/"], ["", "a", "a/b/c", "/"]),
            _gc("a**b", ["ab", "axxb", "a/b"], ["ab", "axxb"]),
            _gc("x/***/y", ["x/q/y", "x/q/r/y", "x/y"], ["x/q/y"]),
            _gc("**/**/c", ["c", "a/b/c"], ["c", "a/b/c"]),
        ])),
        Test("功能", "以 . 开头的路径段只能被字面量 . 匹配（* / ? / [...] / ** 都不行）", _cases(F, [
            _gc("*", ["a", ".a", "..", ""], ["a", ""]),
            _gc(".*", [".a", "a", ".."], [".a", ".."]),
            _gc("\\.a", [".a"], [".a"]),
            _gc("[.]a", [".a", "xa"], []),
            _gc("?a", [".a", "xa"], ["xa"]),
            _gc("**/x", ["x", "a/x", ".a/x", "a/.b/x"], ["x", "a/x"]),
            _gc("src/*", ["src/.env", "src/main"], ["src/main"]),
            _gc("a/**", ["a/.git", "a/b", "a/b/.c"], ["a/b"]),
            _gc(".git/**", [".git/config", ".git/.x"], [".git/config"]),
            _gc("a*", ["a.b", ".a"], ["a.b"]),
        ])),
        Test("功能", "空段与边界", _cases(F, [
            _gc("a/*/b", ["a//b", "a/x/b"], ["a//b", "a/x/b"]),
            _gc("", ["", "a", "/"], [""]),
            _gc("*/a", ["/a", "x/a"], ["/a", "x/a"]),
            _gc("a/", ["a/", "a"], ["a/"]),
            _gc("/**", ["/", "/a", "a"], ["/", "/a"]),
        ])),
        Test("功能", "非法模式抛出 ValueError（即使 paths 为空）", _cases(F, [
            _gc("[a", [], VE), _gc("a\\", [], VE), _gc("[!]", ["x"], VE), _gc("x/[b/c]", [], VE),
            _gc("\\", ["x"], VE), _gc("ok/**/[", [], VE), _gc("[a\\]", ["a"], VE),
        ])),
        Test("功能", "保持原顺序、保留重复", _cases(F, [
            _gc("*.py", ["b.py", "a.py", "b.py", "c.txt"], ["b.py", "a.py", "b.py"]),
        ])),
        Test("功能", "随机对拍（120 组）", _cases(F, _random_cases(_rand_t2, 120, 202)), weight=3),
        Test("隐性", "长模式与长路径（1500 个 ?）", _cases(F, [
            _gc("?" * 1500, ["x" * 1500, "x" * 1499, "x" * 1501], ["x" * 1500]),
        ])),
        Test("隐性", "不修改入参", _no_mutation(F, _const("*.py", ["b.py", "a.txt"]), ("pattern", "paths"))),
        Test("隐性", "吞吐量：10 万条路径",
             _timed_case(F, lambda: _t2_throughput(), factor=20)),
        Test("安全", "段内回溯攻击（ReDoS）：*a*a*…*b 对 1 万个 a",
             _timed_case(F, lambda: ("*a" * 25 + "*b", ["a" * 10000, "a" * 9999 + "b"]), factor=50, floor=0.5)),
        Test("安全", "段内回溯攻击：*?*?…*x 对 5000 个字符",
             _timed_case(F, lambda: ("*" + "?*" * 30 + "x", ["a" * 5000, "a" * 4999 + "x"]), factor=50, floor=0.5)),
        Test("安全", "段级回溯攻击：**/a/**/a/…/b 对 3000 段",
             _timed_case(F, lambda: ("/".join(["**", "a"] * 15 + ["b"]), ["/".join(["a"] * 3000),
                                                                     "/".join(["a"] * 2999 + ["b"])]),
                         factor=50, floor=0.5)),
    ]


# ---------- T3 run_book ----------

def _L(oid, owner, side, price, qty, tif="GTC"):
    return {"op": "limit", "id": oid, "owner": owner, "side": side, "price": price, "qty": qty, "tif": tif}


def _M(oid, owner, side, qty):
    return {"op": "market", "id": oid, "owner": owner, "side": side, "qty": qty}


def _X(oid):
    return {"op": "cancel", "id": oid}


def _A(oid, qty):
    return {"op": "amend", "id": oid, "qty": qty}


def _book(label, cmds, events, bids, asks):
    return _c(label, _V((events, {"bids": bids, "asks": asks})), cmds)


def _rand_t3(rng):
    prices = ["1", "1.0", "1.5", "1.50", "2", "2.25", "3", "0.5", "007", "2.00000001"]
    owners = ["A", "B", "C"]
    cmds, ids = [], []
    for i in range(rng.randint(5, 60)):
        r = rng.random()
        if r < 0.55:
            oid = "o%d" % i if (rng.random() > 0.05 or not ids) else rng.choice(ids)
            cmds.append(_L(oid, rng.choice(owners), rng.choice(["buy", "sell"]), rng.choice(prices),
                           rng.randint(1, 6), rng.choice(["GTC", "GTC", "GTC", "IOC", "FOK"])))
            ids.append(oid)
        elif r < 0.65:
            cmds.append(_M("m%d" % i, rng.choice(owners), rng.choice(["buy", "sell"]), rng.randint(1, 10)))
            ids.append("m%d" % i)
        elif r < 0.8:
            cmds.append(_X(rng.choice(ids) if ids and rng.random() < 0.9 else "zz"))
        elif r < 0.9:
            cmds.append(_A(rng.choice(ids) if ids else "zz", rng.choice([0, 1, 2, 3, 5, 8])))
        else:
            base = _L("x%d" % i, "A", "buy", "1", 1)
            k = rng.choice(["qty", "price", "side", "tif", "op"])
            base[k] = rng.choice({"qty": [0, -1, True, 2.0], "side": ["BUY", None], "tif": ["DAY", None],
                                  "price": ["0", "0.000", "-1", "1e2", "1.123456789", " 1", "1.", ".5", "١", 1],
                                  "op": ["modify", None]}[k])
            cmds.append(base)
    return (cmds,)


def _t3_stream(seed, n, cancel_ratio=0.25, fok_ratio=0.02):
    """大规模随机指令流：价格围绕中间价随机游走，深盘口，大量撤单与改量。"""
    rng = random.Random(seed)
    cmds, live = [], []
    mid = 100000
    for i in range(n):
        r = rng.random()
        if r < cancel_ratio and live:
            j = rng.randrange(len(live))
            live[j], live[-1] = live[-1], live[j]
            cmds.append(_X(live.pop()))
        elif r < cancel_ratio + 0.05 and live:
            cmds.append(_A(rng.choice(live), rng.randint(1, 50)))
        elif r < cancel_ratio + 0.08:
            cmds.append(_M("m%d" % i, "u%d" % rng.randrange(50), rng.choice(["buy", "sell"]), rng.randint(1, 200)))
        else:
            mid += rng.randint(-3, 3)
            side = rng.choice(["buy", "sell"])
            tif = "FOK" if rng.random() < fok_ratio else ("IOC" if rng.random() < 0.05 else "GTC")
            off = rng.randint(-20, 400) if tif != "FOK" else -rng.randint(300, 600)  # FOK 深入对手盘
            p = mid - off if side == "buy" else mid + off
            oid = "o%d" % i
            cmds.append(_L(oid, "u%d" % rng.randrange(50), side, "%d.%02d" % divmod(max(p, 1), 100),
                           rng.randint(1, 50) if tif != "FOK" else rng.randint(1, 20), tif))
            if tif == "GTC":
                live.append(oid)
    return cmds


def _tests_t3():
    F = "run_book"
    VB = "buy"
    VS = "sell"
    return [
        Test("功能", "价格优先、成交价取挂单价格、完全成交不产生额外事件", _cases(F, [
            _book("吃两个价位", [_L("s1", "A", VS, "10.5", 5), _L("s2", "B", VS, "10", 3), _L("b1", "C", VB, "11", 6)],
                  [("rest", "s1", "10.5", 5), ("rest", "s2", "10", 3), ("trade", "b1", "s2", "10", 3),
                   ("trade", "b1", "s1", "10.5", 3)], [], [("10.5", 2, 1)]),
        ])),
        Test("功能", "同价位时间优先，部分成交后保留优先级", _cases(F, [
            _book("时间优先", [_L("s1", "A", VS, "10", 5), _L("s2", "B", VS, "10", 5), _L("b1", "C", VB, "10", 3),
                           _L("b2", "C", VB, "10", 4)],
                  [("rest", "s1", "10", 5), ("rest", "s2", "10", 5), ("trade", "b1", "s1", "10", 3),
                   ("trade", "b2", "s1", "10", 2), ("trade", "b2", "s2", "10", 2)], [], [("10", 3, 1)]),
        ])),
        Test("功能", "GTC 剩余挂单、IOC 剩余撤销", _cases(F, [
            _book("GTC/IOC", [_L("s1", "A", VS, "10", 2), _L("b1", "B", VB, "10", 5), _L("s2", "C", VS, "9", 10, "IOC")],
                  [("rest", "s1", "10", 2), ("trade", "b1", "s1", "10", 2), ("rest", "b1", "10", 3),
                   ("trade", "b1", "s2", "10", 3), ("cancel", "s2", 7, "ioc")], [], []),
        ])),
        Test("功能", "市价单吃多个价位，剩余 no_liquidity；空簿市价单", _cases(F, [
            _book("市价", [_L("s1", "A", VS, "1", 2), _L("s2", "A", VS, "2", 2), _M("m1", "B", VB, 5), _M("m2", "B", VS, 3)],
                  [("rest", "s1", "1", 2), ("rest", "s2", "2", 2), ("trade", "m1", "s1", "1", 2),
                   ("trade", "m1", "s2", "2", 2), ("cancel", "m1", 1, "no_liquidity"),
                   ("cancel", "m2", 3, "no_liquidity")], [], []),
        ])),
        Test("功能", "FOK：数量不足时整单取消且簿不变；足够时跨价位完全成交", _cases(F, [
            _book("FOK", [_L("s1", "A", VS, "10", 2), _L("s2", "B", VS, "11", 2), _L("f1", "C", VB, "11", 5, "FOK"),
                          _L("f2", "C", VB, "11", 4, "FOK")],
                  [("rest", "s1", "10", 2), ("rest", "s2", "11", 2), ("cancel", "f1", 5, "fok"),
                   ("trade", "f2", "s1", "10", 2), ("trade", "f2", "s2", "11", 2)], [], []),
            _book("FOK 只计价格可成交的单", [_L("s1", "A", VS, "10", 2), _L("s2", "B", VS, "12", 5),
                                     _L("f1", "C", VB, "11", 3, "FOK")],
                  [("rest", "s1", "10", 2), ("rest", "s2", "12", 5), ("cancel", "f1", 3, "fok")],
                  [], [("10", 2, 1), ("12", 5, 1)]),
        ])),
        Test("功能", "自成交保护：撤掉自己的挂单后继续撮合", _cases(F, [
            _book("STP", [_L("s1", "A", VS, "10", 2), _L("s2", "B", VS, "10", 2), _L("b1", "A", VB, "10", 3)],
                  [("rest", "s1", "10", 2), ("rest", "s2", "10", 2), ("cancel", "s1", 2, "self_trade"),
                   ("trade", "b1", "s2", "10", 2), ("rest", "b1", "10", 1)], [("10", 1, 1)], []),
        ])),
        Test("功能", "FOK + 自成交：自己的单不计入可成交量，取消时不撤自己的单", _cases(F, [
            _book("FOK+STP", [_L("s1", "A", VS, "10", 3), _L("s2", "B", VS, "10", 1), _L("f1", "A", VB, "10", 2, "FOK"),
                              _L("f2", "A", VB, "10", 1, "FOK")],
                  [("rest", "s1", "10", 3), ("rest", "s2", "10", 1), ("cancel", "f1", 2, "fok"),
                   ("cancel", "s1", 3, "self_trade"), ("trade", "f2", "s2", "10", 1)], [], []),
        ])),
        Test("功能", "撤单：部分成交后的剩余、未知 id、已成交 id", _cases(F, [
            _book("撤单", [_L("s1", "A", VS, "10", 5), _L("b1", "B", VB, "10", 2), _X("s1"), _X("s1"), _X("b1"), _X("zz")],
                  [("rest", "s1", "10", 5), ("trade", "b1", "s1", "10", 2), ("cancel", "s1", 3, "user"),
                   ("reject", "s1", "unknown_order"), ("reject", "b1", "unknown_order"),
                   ("reject", "zz", "unknown_order")], [], []),
        ])),
        Test("功能", "改量：减少/不变保持优先级，增加排到队尾", _cases(F, [
            _book("改量", [_L("s1", "A", VS, "10", 5), _L("s2", "B", VS, "10", 5), _A("s1", 3), _L("b1", "C", VB, "10", 1),
                         _A("s1", 6), _L("b2", "C", VB, "10", 1), _A("s2", 4), _L("b3", "C", VB, "10", 1)],
                  [("rest", "s1", "10", 5), ("rest", "s2", "10", 5), ("amend", "s1", 3), ("trade", "b1", "s1", "10", 1),
                   ("amend", "s1", 6), ("trade", "b2", "s2", "10", 1), ("amend", "s2", 4),
                   ("trade", "b3", "s2", "10", 1)], [], [("10", 9, 2)]),
        ])),
        Test("功能", "改量的拒绝（未知 id 优先于 bad_qty）", _cases(F, [
            _book("改量拒绝", [_A("zz", 5), _L("s1", "A", VS, "10", 5), _A("s1", 0), _A("s1", True), _A("s1", 2.0),
                           _A("zz", 0)],
                  [("reject", "zz", "unknown_order"), ("rest", "s1", "10", 5), ("reject", "s1", "bad_qty"),
                   ("reject", "s1", "bad_qty"), ("reject", "s1", "bad_qty"), ("reject", "zz", "unknown_order")],
                  [], [("10", 5, 1)]),
        ])),
        Test("功能", "校验：拒绝原因及其优先顺序", _cases(F, [
            _book("校验", [
                dict(_L("x1", "A", VB, "1", 1), side="BUY"), dict(_L("x2", "A", VB, "1", 1), tif="DAY"),
                dict(_L("x3", "A", VB, "1", 1), op="modify"), _L("x4", "A", VB, "1", 0), _L("x5", "A", VB, "1", True),
                _L("x6", "A", VB, "1", 1.0), dict(_L("x7", "A", VB, "1", 0), side="up"), _L("x8", "A", VB, "0", 1),
                _L("x9", "A", VB, "0.00", 1), _L("x10", "A", VB, "-1", 1), _L("x11", "A", VB, "1e3", 1),
                _L("x12", "A", VB, "1.123456789", 1), _L("x13", "A", VB, " 1", 1), _L("x14", "A", VB, "1.", 1),
                _L("x15", "A", VB, ".5", 1), _L("x16", "A", VB, 5, 1), _L("x17", "A", VB, "x", 0),
                dict(_M("x18", "A", VS, 2), price="garbage", tif="FOK")],
                [("reject", "x1", "bad_order"), ("reject", "x2", "bad_order"), ("reject", "x3", "bad_order"),
                 ("reject", "x4", "bad_qty"), ("reject", "x5", "bad_qty"), ("reject", "x6", "bad_qty"),
                 ("reject", "x7", "bad_order"), ("reject", "x8", "bad_price"), ("reject", "x9", "bad_price"),
                 ("reject", "x10", "bad_price"), ("reject", "x11", "bad_price"), ("reject", "x12", "bad_price"),
                 ("reject", "x13", "bad_price"), ("reject", "x14", "bad_price"), ("reject", "x15", "bad_price"),
                 ("reject", "x16", "bad_price"), ("reject", "x17", "bad_qty"), ("cancel", "x18", 2, "no_liquidity")],
                [], []),
        ])),
        Test("功能", "重复 id：成交过 / 被 FOK 取消的 id 仍被占用；被拒绝的 id 可以复用", _cases(F, [
            _book("重复 id", [_L("o1", "A", VS, "10", 1), _L("o2", "B", VB, "10", 1), _L("o1", "C", VS, "11", 1),
                            _L("f1", "A", VB, "1", 5, "FOK"), _L("f1", "A", VB, "1", 1), _L("r1", "A", VB, "0", 1),
                            _L("r1", "A", VB, "1", 1), _M("o2", "C", VS, 1)],
                  [("rest", "o1", "10", 1), ("trade", "o2", "o1", "10", 1), ("reject", "o1", "duplicate_id"),
                   ("cancel", "f1", 5, "fok"), ("reject", "f1", "duplicate_id"), ("reject", "r1", "bad_price"),
                   ("rest", "r1", "1", 1), ("reject", "o2", "duplicate_id")], [("1", 1, 1)], []),
        ])),
        Test("功能", "价格规范形式；数值相等的价格属于同一价位", _cases(F, [
            _book("规范价格", [_L("s1", "A", VS, "010.50", 1), _L("s2", "B", VS, "10.5", 2), _L("s3", "B", VS, "7.000", 1),
                           _L("s4", "B", VS, "0.10", 1), _L("b1", "C", VB, "10.50000000", 3)],
                  [("rest", "s1", "10.5", 1), ("rest", "s2", "10.5", 2), ("rest", "s3", "7", 1), ("rest", "s4", "0.1", 1),
                   ("trade", "b1", "s4", "0.1", 1), ("trade", "b1", "s3", "7", 1), ("trade", "b1", "s1", "10.5", 1)],
                  [], [("10.5", 2, 1)]),
        ])),
        Test("功能", "随机对拍（80 组）", _cases(F, _random_cases(_rand_t3, 80, 303, show=300)), weight=3),
        Test("隐性", "高精度价格（不能用浮点数）", _cases(F, [
            _book("1 亿量级 + 8 位小数", [_L("s1", "A", VS, "123456789.12345679", 1), _L("s2", "B", VS, "123456789.12345678", 1),
                                  _L("b1", "C", VB, "123456789.12345678", 2, "IOC")],
                  [("rest", "s1", "123456789.12345679", 1), ("rest", "s2", "123456789.12345678", 1),
                   ("trade", "b1", "s2", "123456789.12345678", 1), ("cancel", "b1", 1, "ioc")],
                  [], [("123456789.12345679", 1, 1)]),
            ("随机高精度", lambda: ([_L("p%d" % i, "u%d" % (i % 3), ("buy", "sell")[i % 2],
                                     "99999999.9999999%d" % (i % 10), 1 + i % 4, "GTC") for i in range(40)],), REF),
        ])),
        Test("隐性", "只允许 ASCII 数字；bool 不是 int", _cases(F, [
            _book("非 ASCII", [_L("u1", "A", VB, "١٢", 1), _L("u2", "A", VB, "１２", 1),
                             _L("u3", "A", VB, "12", True), _A("u3", 1)],
                  [("reject", "u1", "bad_price"), ("reject", "u2", "bad_price"), ("reject", "u3", "bad_qty"),
                   ("reject", "u3", "unknown_order")], [], []),
        ])),
        Test("隐性", "不修改入参", _no_mutation(F, lambda: (_rand_t3(random.Random(9))[0],), ("commands",))),
        Test("隐性", "复杂度：10 万条指令、深盘口",
             _timed_case(F, lambda: (_t3_stream(31, 100000),), factor=15)),
        Test("隐性", "复杂度：撤单占一半、撤的是队列中间的订单",
             _timed_case(F, lambda: (_t3_stream(32, 100000, cancel_ratio=0.5),), factor=15)),
        Test("隐性", "复杂度：大量深入对手盘的 FOK（可成交量统计必须提前结束）",
             _timed_case(F, lambda: (_t3_stream(33, 60000, fok_ratio=0.3),), factor=15)),
    ]


# ---------- T4 TTLCache ----------

def _drive_cache(cls, capacity, ops):
    """用假时钟按顺序执行操作：put→None，get→值或 "<miss>"，del→bool，len→int，stats→dict；最后追加一次 stats。"""
    now = [0.0]
    cache = cls(capacity, lambda: now[0])
    out = []
    for op in ops:
        now[0] = op[1]
        kind = op[0]
        try:
            if kind == "put":
                out.append(cache.put(op[2], op[3], op[4], op[5]))
            elif kind == "get":
                out.append(cache.get(op[2], "<miss>"))
            elif kind == "del":
                out.append(cache.delete(op[2]))
            elif kind == "len":
                out.append(len(cache))
            else:
                out.append(cache.stats())
        except ValueError:
            out.append("ValueError")
    out.append(cache.stats())
    return out


def _cache_call(cls, args):
    return _drive_cache(cls, *args)


def _st(h, m, ev, ex, size, count):
    return {"hits": h, "misses": m, "evictions": ev, "expirations": ex, "size": size, "count": count}


def _cc(label, capacity, ops, expected):
    return (label, _const(capacity, ops), _V(expected) if expected is not REF else REF)


def _rand_t4(rng):
    cap = rng.randint(3, 12)
    ops, t = [], 0.0
    for _ in range(rng.randint(5, 60)):
        t += rng.choice([0, 0, 0.5, 1, 1, 2, 3])
        r = rng.random()
        k = rng.choice("abcdef")
        if r < 0.4:
            ops.append(("put", t, k, rng.randint(0, 99), rng.choice([1, 1, 2, 3, 5, cap + 1]), rng.choice([1, 2, 3, 0.5, 10])))
        elif r < 0.72:
            ops.append(("get", t, k))
        elif r < 0.82:
            ops.append(("del", t, k))
        elif r < 0.9:
            ops.append(("len", t))
        elif r < 0.96:
            ops.append(("stats", t))
        else:
            ops.append(("put", t, k, 1, rng.choice([0, -1, True, 1.5, 1]), rng.choice([0, -1, True, float("nan"), 1])))
    return (cap, ops)


def _t4_validation(impl, ref):
    cls = _get_fn(impl, "TTLCache")
    fails = []
    for cap in (0, -1, True, 2.5, "3", None):
        got = _outcome(cls, (cap, lambda: 0.0))
        m = _judge_outcome(got, _E(ValueError))
        if m:
            fails.append("[capacity=%r] %s" % (cap, m))
    got = _outcome(_drive_cache, (cls, 5, [("put", 0, "a", 1, 2, 10)] +
                                  [("put", 0, "b", 1, s, 10) for s in (0, -1, True, 1.5, "1")] +
                                  [("put", 0, "c", 1, 1, t) for t in (0, -1, True, float("nan"), "1", None)] +
                                  [("get", 1, "a")]))
    exp = [None] + ["ValueError"] * 11 + [1, _st(1, 0, 0, 0, 2, 1)]
    m = _judge_outcome(got, _V(exp))
    if m:
        fails.append("[put 参数校验] " + m)
    return ("fail", "\n    ".join(fails)) if fails else ("pass", "")


def _t4_clock_calls(impl, ref):
    cls = _get_fn(impl, "TTLCache")
    calls = [0]

    def clock():
        calls[0] += 1
        return float(calls[0])
    problems = []

    def expect(label, fn, args, n):
        before = calls[0]
        _outcome(fn, args)
        used = calls[0] - before
        if used != n:
            problems.append("%s 调用了 clock() %d 次（应为 %d 次）" % (label, used, n))
    got = _outcome(cls, (10, clock))
    if got[0] == "exc":
        return "fail", "构造失败: " + _fmt_exc(got[1])
    c = got[1]
    if calls[0]:
        problems.append("构造函数调用了 clock() %d 次（应为 0 次）" % calls[0])
    expect("put", c.put, ("a", 1, 2, 100), 1)
    expect("put（覆盖并触发淘汰）", c.put, ("b", 1, 9, 1), 1)
    expect("get 命中", c.get, ("b",), 1)
    expect("get 未命中", c.get, ("zz",), 1)
    expect("delete", c.delete, ("b",), 1)
    expect("len()", len, (c,), 1)
    expect("stats()", c.stats, (), 1)
    expect("put 参数非法", c.put, ("x", 1, 0, 1), 0)
    expect("put 参数非法（ttl）", c.put, ("x", 1, 1, -1), 0)
    return ("fail", "\n    ".join(problems)) if problems else ("pass", "")


def _t4_instances(impl, ref):
    cls = _get_fn(impl, "TTLCache")
    c1, c2 = cls(10, lambda: 0.0), cls(10, lambda: 0.0)
    c1.put("k", "v", 1, 10)
    got = (c2.get("k", "<miss>"), len(c2), c2.stats())
    exp = ("<miss>", 0, _st(0, 1, 0, 0, 0, 0))
    m = _judge_outcome(("ok", got), _V(exp))
    return ("fail", "两个实例之间共享了状态: " + m) if m else ("pass", "")


def _t4_threads(impl, ref):
    cls = _get_fn(impl, "TTLCache")
    old = sys.getswitchinterval()
    sys.setswitchinterval(1e-6)
    try:
        ticker = itertools.count()
        clock = lambda: next(ticker) * 1e-3  # noqa: E731  单调递增，next() 在 CPython 中是原子的
        cache = cls(400, clock)
        n_threads, n_ops = 8, 3000
        errors, gets = [], [0] * n_threads
        start = threading.Barrier(n_threads)

        def worker(t):
            rng = random.Random(t)
            try:
                start.wait()
                for i in range(n_ops):
                    k = rng.randrange(300)
                    r = rng.random()
                    if r < 0.5:
                        v = cache.get(k)
                        gets[t] += 1
                        if v is not None and v[0] != k:
                            errors.append("get(%r) 读到了别的键的值 %r" % (k, v))
                    elif r < 0.9:
                        cache.put(k, (k, t, i), rng.randint(1, 4), rng.choice([0.05, 1.0, 100.0]))
                    elif r < 0.97:
                        cache.delete(k)
                    else:
                        len(cache)
            except Exception as e:
                errors.append("线程 %d 抛出 %s" % (t, _fmt_exc(e)))
        threads = [threading.Thread(target=worker, args=(t,)) for t in range(n_threads)]
        for th in threads:
            th.start()
        for th in threads:
            th.join()
        if errors:
            return "fail", "并发执行时出错（%d 处），例如: %s" % (len(errors), errors[0])
        st = cache.stats()
        problems = []
        if st["hits"] + st["misses"] != sum(gets):
            problems.append("hits + misses = %d，但实际调用了 %d 次 get（统计丢失更新）" % (st["hits"] + st["misses"], sum(gets)))
        if st["size"] > 400:
            problems.append("size = %d 超过 capacity 400" % st["size"])
        n = len(cache)
        if st["count"] < n:
            problems.append("stats 的 count (%d) 与 len (%d) 不一致" % (st["count"], n))
        return ("fail", "；".join(problems)) if problems else ("pass", "")
    finally:
        sys.setswitchinterval(old)


def _t4_ops_many_entries(seed, n):
    rng = random.Random(seed)
    ops, t = [], 0.0
    for i in range(n):
        t += 0.001
        if i % 40 == 39:
            ops.append(("len", t) if i % 80 == 79 else ("stats", t))
        elif rng.random() < 0.7:
            ops.append(("put", t, i, i, 1, rng.choice([0.5, 5.0, 50.0, 500.0])))
        else:
            ops.append(("get", t, rng.randrange(i + 1)))
    return (10 ** 9, ops)


def _t4_ops_eviction(seed, n, capacity):
    rng = random.Random(seed)
    ops, t = [], 0.0
    for i in range(n):
        t += 0.001
        k = rng.randrange(3 * capacity)
        if rng.random() < 0.55:
            ops.append(("put", t, k, i, rng.randint(1, 3), 1e6))
        else:
            ops.append(("get", t, k))
    return (capacity, ops)


def _tests_t4():
    F = "TTLCache"
    C = _cache_call
    return [
        Test("功能", "基本 put / get / stats", _cases(F, [
            _cc("基本", 10, [("put", 0, "a", "A", 1, 10), ("get", 1, "a"), ("get", 1, "b")],
                [None, "A", "<miss>", _st(1, 1, 0, 0, 1, 1)]),
        ], call=C)),
        Test("功能", "LRU 淘汰顺序（get 命中会刷新最近使用）", _cases(F, [
            _cc("LRU", 3, [("put", 0, "a", 1, 1, 100), ("put", 0, "b", 2, 1, 100), ("put", 0, "c", 3, 1, 100),
                           ("get", 1, "a"), ("put", 2, "d", 4, 1, 100), ("get", 3, "b"), ("get", 3, "a"),
                           ("get", 3, "c"), ("get", 3, "d")],
                [None, None, None, 1, None, "<miss>", 1, 3, 4, _st(4, 1, 1, 0, 3, 3)]),
        ], call=C)),
        Test("功能", "过期边界：now == expire_at 时已过期", _cases(F, [
            _cc("边界", 10, [("put", 0, "a", 1, 1, 5), ("get", 4.999, "a"), ("get", 5, "a")],
                [None, 1, "<miss>", _st(1, 1, 0, 1, 0, 0)]),
        ], call=C)),
        Test("功能", "超出容量时先清除过期条目，仍超出才淘汰最久未用的", _cases(F, [
            _cc("先清过期", 3, [("put", 0, "a", 1, 2, 1), ("put", 0, "b", 2, 1, 100), ("put", 2, "c", 3, 1, 100),
                             ("get", 2, "b")],
                [None, None, None, 2, _st(1, 0, 0, 1, 2, 2)]),
            _cc("未超容量不清理", 10, [("put", 0, "a", 1, 1, 1), ("put", 5, "b", 2, 1, 100), ("stats", 5)],
                [None, None, _st(0, 0, 0, 1, 1, 1), _st(0, 0, 0, 1, 1, 1)]),
            _cc("清完过期仍超出", 4, [("put", 0, "a", 1, 2, 1), ("put", 0, "b", 2, 2, 100), ("put", 3, "c", 3, 3, 100)],
                [None, None, None, _st(0, 0, 1, 1, 3, 1)]),
        ], call=C)),
        Test("功能", "size 大于 capacity：不存入，并且删除该 key 的旧条目", _cases(F, [
            _cc("超大条目", 5, [("put", 0, "a", 1, 1, 10), ("put", 0, "a", 2, 6, 10), ("get", 1, "a")],
                [None, None, "<miss>", _st(0, 1, 0, 0, 0, 0)]),
        ], call=C)),
        Test("功能", "覆盖已有 key：更新值、大小、过期时间，成为最近使用；覆盖已过期条目不计统计", _cases(F, [
            _cc("覆盖", 3, [("put", 0, "a", "old", 1, 10), ("put", 0, "b", 2, 1, 100), ("put", 0, "c", 3, 1, 100),
                          ("put", 1, "a", "new", 1, 100), ("put", 2, "d", 4, 1, 100), ("get", 50, "a"), ("get", 50, "b")],
                [None, None, None, None, None, "new", "<miss>", _st(1, 1, 1, 0, 3, 3)]),
            _cc("覆盖过期条目", 10, [("put", 0, "x", 1, 1, 1), ("put", 5, "x", 2, 1, 1), ("get", 5.5, "x")],
                [None, None, 2, _st(1, 0, 0, 0, 1, 1)]),
        ], call=C)),
        Test("功能", "delete 的三种情况", _cases(F, [
            _cc("delete", 10, [("put", 0, "a", 1, 1, 10), ("put", 0, "b", 1, 1, 1), ("del", 2, "a"), ("del", 2, "b"),
                               ("del", 2, "c")],
                [None, None, True, False, False, _st(0, 0, 0, 1, 0, 0)]),
        ], call=C)),
        Test("功能", "len / stats 会先清除过期条目", _cases(F, [
            _cc("len", 10, [("put", 0, "a", 1, 3, 1), ("put", 0, "b", 1, 2, 10), ("len", 0.5), ("len", 1), ("stats", 20)],
                [None, None, 2, 1, _st(0, 0, 0, 2, 0, 0), _st(0, 0, 0, 2, 0, 0)]),
        ], call=C)),
        Test("功能", "get 的 default；值可以是 None；key 可以是任意可哈希对象", _cases(F, [
            _cc("None 值", 10, [("put", 0, ("t", 1), None, 1, 10), ("get", 1, ("t", 1)), ("put", 1, 7, "seven", 1, 10),
                              ("get", 1, 7.0)],
                [None, None, None, "seven", _st(2, 0, 0, 0, 2, 2)]),
        ], call=C)),
        Test("功能", "参数校验（ValueError，且缓存不变）", _t4_validation),
        Test("功能", "随机对拍（80 组）", _cases(F, _random_cases(_rand_t4, 80, 404, show=300), call=C), weight=3),
        Test("隐性", "每次方法调用恰好调用一次 clock()（构造和校验失败时不调用）", _t4_clock_calls),
        Test("隐性", "多个实例之间互不影响", _t4_instances),
        Test("隐性", "多线程并发：8 个线程同时读写", _t4_threads),
        Test("隐性", "复杂度：20 万条目，频繁调用 len() / stats()",
             _timed_case(F, lambda: _t4_ops_many_entries(41, 200000), factor=15, call=C)),
        Test("隐性", "复杂度：容量 5 万、持续淘汰",
             _timed_case(F, lambda: _t4_ops_eviction(42, 200000, 50000), factor=15, call=C)),
    ]


# ---------- T5 expand ----------

def _rand_t5_tpl(rng):
    pieces = ["x", "yy", "$$", "$", "}", "${a}", "${b}", "${c}", "${a}", "${b}", "${zz}", "${a:-Q}", "${zz:-D}",
              "${zz:-${b}}", "${zz:-${zz:-${c}}}", "${a:-}", "{", "$x"]
    if rng.random() < 0.15:
        pieces = pieces + ["${", "${1}", "${a b}", "${a:-"]
    return "".join(rng.choice(pieces) for _ in range(rng.randint(0, 6)))


def _rand_t5(rng):
    variables = {n: _rand_t5_tpl(rng) for n in rng.sample("abcd", rng.randint(0, 4))}
    return (_rand_t5_tpl(rng), variables, rng.randint(0, 40))


def _ex(label, exp, template, variables, limit=1000):
    return _c(label, exp if isinstance(exp, tuple) else _V(exp), template, variables, limit)


def _t5_memory_case(variables, template, limit, max_peak_floor=8 * 2 ** 20):
    def run(impl, ref):
        fn = _get_fn(impl, "expand")
        results = []
        for f in (ref["expand"], fn):
            args = (template, copy.deepcopy(variables), limit)
            gc.collect()
            tracemalloc.start()
            try:
                t0 = time.perf_counter()
                got = _outcome(f, args)
                sec = time.perf_counter() - t0
                peak = tracemalloc.get_traced_memory()[1]
            finally:
                tracemalloc.stop()
            results.append((got, peak, sec))
        (rgot, rpeak, rsec), (cgot, cpeak, csec) = results
        msg = _judge_outcome(cgot, _V(rgot[1]) if rgot[0] == "ok" else _E(type(rgot[1])))
        cap = max(max_peak_floor, 10 * rpeak)
        if cgot[0] == "exc" and not isinstance(cgot[1], ValueError):
            return "fail", msg
        if cpeak > cap:
            return "fail", "内存峰值 %.1f MB，超过上限 %.1f MB（标准实现 %.2f MB）——在确认超过 limit 之前构造了超长字符串" % (
                cpeak / 2 ** 20, cap / 2 ** 20, rpeak / 2 ** 20)
        if csec > max(0.5, 50 * rsec):
            return "fail", "耗时 %s（标准实现 %s）" % (_ft(csec), _ft(rsec))
        if msg:
            return "partial", "内存与耗时达标，但结果不正确（得一半分）: " + msg
        return "pass", "内存峰值 %.2f MB，耗时 %s" % (cpeak / 2 ** 20, _ft(csec))
    return run


_LOCKED_RECURSION = 4000


def _call_recursion_locked(fn, args):
    """调用期间把递归上限锁定为 _LOCKED_RECURSION，并让 sys.setrecursionlimit 失效。

    Python 3.12+ 的纯 Python 递归不占 C 栈，调高递归上限后 10 万层递归“碰巧”能跑；
    但在 3.8~3.11 上同样的代码会段错误。锁定上限让结果与解释器版本无关。"""
    old_limit, setter = sys.getrecursionlimit(), sys.setrecursionlimit
    setter(_LOCKED_RECURSION)
    sys.setrecursionlimit = lambda limit: None
    try:
        return fn(*args)
    finally:
        sys.setrecursionlimit = setter
        setter(old_limit)


def _t5_chain(n):
    v = {"v0": "x"}
    for i in range(1, n):
        v["v%d" % i] = "${v%d}" % (i - 1)
    return ("[${v%d}]" % (n - 1), v, 100)


def _t5_wide():
    v = {"w": "xy", "v": "${w}${w}"}
    return ("${v}" * 50000, v, 10 ** 6)


def _tests_t5():
    F = "expand"
    VE = _E(ValueError)
    laughs_1000 = {"v0": "x" * 100, "v1": "${v0}" * 1000, "v2": "${v1}" * 1000}
    laughs_10 = {"w0": "x" * 10}
    for i in range(1, 8):
        laughs_10["w%d" % i] = "${w%d}" * 10 % ((i - 1,) * 10)
    zero = {"z0": ""}
    for i in range(1, 81):
        zero["z%d" % i] = "${z%d}${z%d}" % (i - 1, i - 1)
    return [
        Test("功能", "基本引用与字面量", _cases(F, [
            _ex("Hello", "Hello World!", "Hello ${name}!", {"name": "World"}),
            _ex("多个引用", "1-2-1", "${a}-${b}-${a}", {"a": "1", "b": "2"}),
            _ex("无引用", "plain text", "plain text", {}),
            _ex("空模板", "", "", {"a": "1"}),
        ])),
        Test("功能", "$$ 转义与孤立的 $", _cases(F, [
            _ex("$$", "$", "$$", {}),
            _ex("$${a}", "${a}", "$${a}", {"a": "X"}),
            _ex("$$${a}", "$X", "$$${a}", {"a": "X"}),
            _ex("孤立 $", "cost: 5$ and $x and a$", "cost: 5$ and $x and a$", {}),
            _ex("$$$$", "$$", "$$$$", {}),
        ])),
        Test("功能", "默认值（含嵌套、空默认值、默认值中的 $$ 和 {）", _cases(F, [
            _ex("缺失用默认", "fallback", "${missing:-fallback}", {}),
            _ex("存在不用默认", "A", "${a:-fallback}", {"a": "A"}),
            _ex("空默认", "<>", "<${m:-}>", {}),
            _ex("默认里有引用", "xAy", "${m:-x${a}y}", {"a": "A"}),
            _ex("嵌套默认", "deep", "${m:-${n:-deep}}", {}),
            _ex("默认里的 $$", "$", "${m:-$$}", {}),
            _ex("默认里的 {", "a{bc}", "${m:-a{b}c}", {}),
        ])),
        Test("功能", "不在 ${...:- 内部的 } 是字面量", _cases(F, [
            _ex("}{}", "}{}", "}{}", {}),
            _ex("a}b", "a}b", "a}b", {}),
            _ex("引用后的 }", "1}", "${a}}", {"a": "1"}),
        ])),
        Test("功能", "变量值也是模板（递归展开）", _cases(F, [
            _ex("递归", "x$-x$", "${a}", {"a": "${b}-${b}", "b": "x$$"}),
            _ex("值里的默认", "DEF", "${a}", {"a": "${nope:-DEF}"}),
        ])),
        Test("功能", "语法错误 → ValueError", _cases(F, [
            _ex(t, VE, t, {"a": "1"}) for t in ["${", "${}", "${1a}", "${a b}", "${a:b}", "${a", "${a:-x",
                                                 "${a:-${b}", "${变量}", "${a-}", "x${:-y}"]
        ])),
        Test("功能", "未定义变量 → ValueError", _cases(F, [
            _ex("直接", VE, "${nope}", {}),
            _ex("间接", VE, "${a}", {"a": "${nope}"}),
        ])),
        Test("功能", "循环引用 → ValueError", _cases(F, [
            _ex("a↔b", VE, "${a}", {"a": "${b}", "b": "${a}"}),
            _ex("自引用", VE, "${a}", {"a": "x${a}"}),
            _ex("经过默认值", VE, "${a}", {"a": "${m:-${a}}"}),
        ])),
        Test("功能", "limit 边界", _cases(F, [
            _ex("恰好等于", "abc", "${a}", {"a": "abc"}, 3),
            _ex("超过", VE, "${a}", {"a": "abcd"}, 3),
            _ex("limit=0 空结果", "", "${a}", {"a": ""}, 0),
            _ex("limit=0 非空", VE, "x", {}, 0),
        ])),
        Test("功能", "随机对拍（150 组）", _cases(F, _random_cases(_rand_t5, 150, 505)), weight=3),
        Test("隐性", "惰性：没用到的变量有语法错误或循环引用也不影响", _cases(F, [
            _ex("惰性", "fine", "${ok}", {"bad": "${", "c1": "${c2}", "c2": "${c1}", "ok": "fine"}),
        ])),
        Test("隐性", "惰性：变量存在时不展开其默认值", _cases(F, [
            _ex("默认值里有未定义变量", "A", "${a:-${undefined}}", {"a": "A"}),
            _ex("默认值里有循环", "A", "${a:-${c1}}", {"a": "A", "c1": "${c1}"}),
        ])),
        Test("隐性", "template 中的默认值必须整体语法正确（即使不会被展开）", _cases(F, [
            _ex("未用到的默认值有语法错误", VE, "${a:-${}}", {"a": "A"}),
        ])),
        Test("隐性", "10 万层变量引用链（递归上限锁定为 %d）" % _LOCKED_RECURSION, _cases(F, [
            ("链", lambda: _t5_chain(100000), _V("[x]")),
        ], call=_call_recursion_locked)),
        Test("隐性", "10 万层默认值嵌套（递归上限锁定为 %d）" % _LOCKED_RECURSION, _cases(F, [
            ("嵌套", lambda: ("${m:-" * 100000 + "x" + "}" * 100000, {}, 10), _V("x")),
        ], call=_call_recursion_locked)),
        Test("隐性", "同一变量被引用 5 万次（必须缓存展开结果）",
             _timed_case(F, _t5_wide, factor=20)),
        Test("隐性", "不修改入参", _no_mutation(F, _const("${a}${b:-x}", {"a": "${c}", "c": "1"}, 100),
                                         ("template", "variables", "limit"))),
        Test("安全", "指数级引用、结果为空（2^80 次引用）", _timed_case(F, lambda: ("<${z80}>", zero, 10), factor=50, floor=0.5)),
        Test("安全", "十亿笑声（扇出 10、深度 7，展开后 1 亿字符，limit 10 万）",
             _t5_memory_case(laughs_10, "${w7}", 100000)),
        Test("安全", "十亿笑声（扇出 1000、深度 2，展开后 1 亿字符，limit 10 万）",
             _t5_memory_case(laughs_1000, "${v2}", 100000)),
    ]
# ════════════════════════════════════════════════════════════════════════════
# 第 7 部分：性能测试数据（原代码在其上能正常跑完，用来计算“相对原代码的加速比”）
# ════════════════════════════════════════════════════════════════════════════

class PerfCase:
    def __init__(self, make, call=None, cleanup=None):
        self.make = make                                   # 每次返回一份新的参数（不计时）
        self.call = call or (lambda fn, args: fn(*args))   # 被计时的调用
        self.cleanup = cleanup or (lambda: None)


def _perf_t1(seed, scale):
    rng = random.Random(seed)
    n = max(60, int(1900 * scale))
    common = ["", "}", "    return result", "    pass", "else:", "{"]
    a = [rng.choice(common) if rng.random() < 0.25 else "stmt_%d(%d)" % (rng.randrange(400), rng.randrange(9))
         for _ in range(n)]
    b = list(a)
    for _ in range(n // 10):
        i = rng.randrange(len(b))
        r = rng.random()
        if r < 0.35:
            del b[i]
        elif r < 0.7:
            b.insert(i, "new_%d" % rng.randrange(10 ** 6))
        else:
            b[i] = rng.choice(common)
    return PerfCase(lambda: (list(a), list(b)))


def _perf_t2(seed, scale):
    rng = random.Random(seed)
    dirs = ["src", "lib", "tests", "docs", "build", "pkg", "core", "util"]
    paths = []
    for _ in range(max(200, int(20000 * scale))):
        segs = [rng.choice(dirs) if rng.random() < 0.6 else "m%d" % rng.randrange(300) for _ in range(rng.randint(1, 5))]
        segs.append(rng.choice(["test_%d.py", "mod%d.c", "mod%d.h", "_priv%d.md", "guide%d.md", ".cfg%d"]) % rng.randrange(50))
        paths.append("/".join(segs))
    patterns = ["src/**/test_*.py", "**/*.[ch]", "docs/**/[!_]*.md", "*/m1*/**"]
    return PerfCase(lambda: (patterns, list(paths)),
                    call=lambda fn, args: [fn(p, args[1]) for p in args[0]])


def _perf_t3(seed, scale):
    cmds = _t3_stream(seed, max(500, int(12000 * scale)))
    return PerfCase(lambda: (copy.deepcopy(cmds),))


def _perf_t4(seed, scale):
    rng = random.Random(seed)
    cap = max(50, int(2000 * scale))
    ops, t = [], 0.0
    for i in range(max(1000, int(60000 * scale))):
        t += 0.01
        k = rng.randrange(3 * cap)
        r = rng.random()
        if r < 0.45:
            ops.append(("put", t, k, i, rng.randint(1, 3), rng.choice([5.0, 50.0, 500.0])))
        elif r < 0.9:
            ops.append(("get", t, k))
        elif r < 0.97:
            ops.append(("del", t, k))
        else:
            ops.append(("stats", t))
    return PerfCase(lambda: (cap, ops), call=_cache_call)


def _perf_t5(seed, scale):
    rng = random.Random(seed)
    layers, width = 11, max(4, int(40 * scale))
    variables = {}
    for lv in range(layers):
        for j in range(width):
            name = "n%d_%d" % (lv, j)
            if lv == 0:
                variables[name] = "leaf%d$$" % j
            else:
                refs = ["${n%d_%d}" % (lv - 1, rng.randrange(width)) for _ in range(2)]
                if rng.random() < 0.3:
                    refs.append("${missing_%d:-${n%d_%d}}" % (j, lv - 1, rng.randrange(width)))
                variables[name] = "<" + "|".join(refs) + ">"
    template = "".join("[${n%d_%d}]" % (layers - 1, rng.randrange(width)) for _ in range(max(20, int(300 * scale))))
    return PerfCase(lambda: (template, dict(variables), 10 ** 9))


# ════════════════════════════════════════════════════════════════════════════
# 第 8 部分：任务注册表
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
    Task("T1", "edit_distance", "文本差异", _tests_t1, _perf_t1),
    Task("T2", "glob_filter", "路径通配", _tests_t2, _perf_t2),
    Task("T3", "run_book", "撮合引擎", _tests_t3, _perf_t3),
    Task("T4", "TTLCache", "过期缓存", _tests_t4, _perf_t4),
    Task("T5", "expand", "模板展开", _tests_t5, _perf_t5),
]
TASK_BY_KEY = {t.key: t for t in TASKS}
FUNC_NAMES = [t.fn for t in TASKS]
# ════════════════════════════════════════════════════════════════════════════
# 第 9 部分：子进程 worker（隔离运行候选代码）
# ════════════════════════════════════════════════════════════════════════════

_WORKER_MEMORY_LIMIT = 4 * 2 ** 30  # 防止失控的候选代码吃光整台机器的内存（仅 POSIX 生效）


def _limit_memory():
    try:
        import resource
        soft, hard = resource.getrlimit(resource.RLIMIT_AS)
        target = _WORKER_MEMORY_LIMIT if hard == resource.RLIM_INFINITY else min(_WORKER_MEMORY_LIMIT, hard)
        if soft == resource.RLIM_INFINITY or soft > target:
            resource.setrlimit(resource.RLIMIT_AS, (target, hard))
    except Exception:
        pass


def _load_impl(spec):
    if spec == "reference":
        return dict(REFERENCE)
    if spec == "baseline":
        mod = types.ModuleType("core_utils_baseline")
        exec(compile(CHALLENGE_CODE, "core_utils.py(原代码)", "exec"), mod.__dict__)
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
        if sum(times) >= 0.6 or len(times) >= 300 or time.perf_counter() - wall0 > 8.0:
            break
    return statistics.median(times), out_hash, len(times)


def _worker_main(cfg):
    proto = os.fdopen(os.dup(sys.stdout.fileno()), "w", encoding="utf-8", buffering=1)
    sys.stdout.flush()
    os.dup2(sys.stderr.fileno(), sys.stdout.fileno())  # 候选代码的 print 一律进 stderr
    _limit_memory()

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
                status, msg = "fail", "候选代码中没有定义 %s" % e
            except BaseException:
                status, msg = "fail", "测试过程中出现未处理的异常:\n" + traceback.format_exc(limit=4)
            send({"type": "result", "i": i, "status": status, "msg": msg, "sec": time.perf_counter() - t0})
        send({"type": "end"})
    else:
        fn = impl.get(task.fn)
        if fn is None:
            send({"type": "perf_error", "rep": 0, "error": "候选代码中没有定义 %s" % task.fn})
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
    """先单独加载一次候选代码：语法错误、导入即崩溃、模块顶层死循环等问题直接判定。"""
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
    streak = 0  # 连续超时次数；连续 3 次超时后，后续测试的超时缩短到 5 秒，避免一个死循环拖慢整轮评测
    while start < n:
        timeout = test_timeout if streak < 3 else min(test_timeout, 5.0)
        w = _Worker({"impl": impl_spec, "task": task.key, "mode": "tests", "start": start}, timeout)
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
                results[idx] = ("fail", "超时（单个测试超过 %gs）：可能死循环、复杂度过高或遭到了攻击输入" % timeout,
                                float(timeout))
                start, streak = idx + 1, streak + 1
            elif t == "exit":
                if current is not None:
                    results[current] = ("fail", "子进程崩溃（退出码 %s），可能是栈溢出 / 内存耗尽 / 段错误 / sys.exit:\n%s"
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
# 第 10 部分：静态审查（只给提示，不扣分）
# ════════════════════════════════════════════════════════════════════════════

def static_review(src):
    notes = []
    try:
        tree = ast.parse(src)
    except SyntaxError as e:
        return ["代码有语法错误: %s" % e]
    top_defs = {n.name for n in tree.body if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef))}
    missing = [f for f in FUNC_NAMES if f not in top_defs]
    if missing:
        notes.append("缺少（或不是模块顶层定义的）函数/类: %s" % ", ".join(missing))
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
                notes.append("第 %s 行：异常被静默吞掉（except ...: pass），请人工确认是否有意为之" % line)
        elif isinstance(node, ast.Call):
            f = node.func
            if isinstance(f, ast.Name) and f.id in ("eval", "exec"):
                notes.append("第 %s 行：调用了 %s()，请人工确认是否安全" % (line, f.id))
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
# 第 11 部分：计分与报告
# ════════════════════════════════════════════════════════════════════════════

W_FUNC, W_HIDDEN, W_PERF, W_BONUS = 35.0, 35.0, 30.0, 20.0
BONUS_DEADZONE = 1.1  # 比标准实现快不到 10% 视为计时噪声，不加分


def _perf_base(s, r):
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
        if t.cat == "安全" and status not in ("pass", "partial"):
            sec_ok = False
        g = groups["func" if t.cat == "功能" else "hidden"]
        g[1] += t.weight
        g[0] += t.weight * {"pass": 1.0, "partial": 0.5}.get(status, 0.0)
    func_ratio = groups["func"][0] / groups["func"][1] if groups["func"][1] else 1.0
    hid_ratio = groups["hidden"][0] / groups["hidden"][1] if groups["hidden"][1] else 1.0
    perf = {"base": perf_b.get("sec"), "ref": perf_r.get("sec"), "cand": perf_c.get("sec"),
            "speedup": None, "ref_speedup": None, "vs_ref": None, "note": "", "valid": False}
    if perf["base"] and perf["ref"]:
        perf["ref_speedup"] = perf["base"] / perf["ref"]
    s_perf = s_bonus = 0.0
    if perf_b.get("error") or perf_r.get("error"):
        perf["note"] = "基准测量失败: %s" % (perf_b.get("error") or perf_r.get("error"))
    elif perf_c.get("error"):
        perf["note"] = perf_c["error"]
    else:
        perf["speedup"] = perf["base"] / perf["cand"] if perf["cand"] else None
        perf["vs_ref"] = perf["ref"] / perf["cand"] if perf["cand"] else None
        correct = perf_c["hashes"] == perf_r["hashes"]
        perf["valid"] = correct
        if not sec_ok:
            perf["note"] = "存在未通过的安全测试，性能分为 0"
        else:
            s_perf = W_PERF * _perf_base(perf["speedup"], perf["ref_speedup"] or 1.0) * func_ratio
            notes = []
            if not correct:
                s_perf *= 0.5
                notes.append("大数据量上的输出与标准答案不一致，性能分减半且无加分")
            elif perf["vs_ref"] and perf["vs_ref"] > BONUS_DEADZONE:
                s_bonus = min(W_BONUS, 10.0 * math.log2(perf["vs_ref"] / BONUS_DEADZONE)) * func_ratio
            if func_ratio < 1:
                notes.append("功能测试通过率 %.0f%%，性能分按比例打折" % (func_ratio * 100))
            if perf["speedup"] is not None and perf["speedup"] < 1:
                notes.append("比原代码更慢")
            perf["note"] = "；".join(notes)
    s_func, s_hidden = W_FUNC * func_ratio, W_HIDDEN * hid_ratio
    return {"func": groups["func"], "hidden": groups["hidden"], "perf": perf,
            "score": {"func": s_func, "hidden": s_hidden, "perf": s_perf, "bonus": s_bonus,
                      "total": s_func + s_hidden + s_perf + s_bonus}}


def _dw(s):
    return sum(2 if unicodedata.east_asian_width(ch) in "WF" else 1 for ch in s)


def _pad(s, width, right=False):
    s = str(s)
    gap = " " * max(0, width - _dw(s))
    return gap + s if right else s + gap


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
    best = max(blocks, key=lambda b: (sum(("def %s(" % f) in b or ("class %s" % f) in b for f in FUNC_NAMES), len(b)))
    return best, True


def load_candidate(path):
    if path in ("@baseline", "@reference"):
        impl = path[1:]
        src = CHALLENGE_CODE if impl == "baseline" else None
        label = "原代码(@baseline)" if impl == "baseline" else "标准答案(@reference)"
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
            log("⚠ %s：缺少 %s" % (c.label, ", ".join(sorted(set(FUNC_NAMES) - set(functions)))))
    for task in tasks:
        log("\n▶ %s（%s）" % (task.label, task.title))
        log("  计时 原代码 ……", end="")
        perf_b = run_perf("baseline", task, reps, scale, timeout=300)
        log(" %s" % (_ft(perf_b.get("sec")) if "sec" in perf_b else perf_b.get("error")), end="")
        log("  | 标准答案 ……", end="")
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
            log("  %s 测试 %d/%d | 耗时 %s | 加速 %s（标准 %s）| 相对标准 %s | 得分 %.1f%s" % (
                _pad(c.label, 22), n_pass, len(results) - n_skip, _ft(p["cand"]), _fx(p["speedup"]),
                _fx(p["ref_speedup"]), _fx(p["vs_ref"]), res["score"]["total"],
                ("  ⚠ " + p["note"].splitlines()[0]) if p["note"] else ""))
    return cands


def _summary(c, tasks):
    """返回 (总分, 候选几何平均加速比, 标准答案在同一批任务上的几何平均加速比, 有效任务数)。"""
    totals = [c.results[t.key]["score"]["total"] for t in tasks]
    valid = [c.results[t.key]["perf"] for t in tasks if c.results[t.key]["perf"]["valid"]]
    return (sum(totals) / len(totals), _geomean([p["speedup"] for p in valid]),
            _geomean([p["ref_speedup"] for p in valid]), len(valid))


def print_report(c, tasks, verbose=False):
    line = "═" * 112
    print("\n" + line)
    print(" 评测报告：%s%s" % (c.label, "（代码提取自 %s → %s）" % (c.extracted_from, c.impl) if c.extracted_from else ""))
    print(line)
    cols = [("任务", 24, False), ("功能", 8, True), ("安全/隐性", 10, True), ("原代码", 9, True),
            ("标准答案", 9, True), ("候选", 9, True), ("加速比", 8, True), ("相对标准", 9, True),
            ("功能", 6, True), ("隐性", 6, True), ("性能", 6, True), ("加分", 6, True), ("得分", 7, True)]
    print("".join(_pad(h, w, r) + " " for h, w, r in cols))
    print("─" * 112)
    for t in tasks:
        r = c.results[t.key]
        p, s = r["perf"], r["score"]
        f_pass = sum(1 for x in r["tests"] if x["cat"] == "功能" and x["status"] == "pass")
        f_all = sum(1 for x in r["tests"] if x["cat"] == "功能" and x["status"] != "skip")
        h_pass = sum(1 for x in r["tests"] if x["cat"] != "功能" and x["status"] == "pass")
        h_all = sum(1 for x in r["tests"] if x["cat"] != "功能" and x["status"] != "skip")
        sp = _fx(p["speedup"]) + ("" if p["valid"] or p["speedup"] is None else "✗")
        row = ["%s %s" % (t.label, t.title), "%d/%d" % (f_pass, f_all), "%d/%d" % (h_pass, h_all),
               _ft(p["base"]), _ft(p["ref"]), _ft(p["cand"]), sp, _fx(p["vs_ref"]),
               "%.1f" % s["func"], "%.1f" % s["hidden"], "%.1f" % s["perf"], "%.1f" % s["bonus"], "%.1f" % s["total"]]
        print("".join(_pad(v, w, rr) + " " for v, (_h, w, rr) in zip(row, cols)))
    print("─" * 112)
    total, gm, gm_ref, n_valid = _summary(c, tasks)
    print(" 总分 %.1f / 100（含性能加分，最高 120）    每个任务 = 功能 %d + 安全/隐性 %d + 性能 %d + 加分 ≤%d"
          % (total, W_FUNC, W_HIDDEN, W_PERF, W_BONUS))
    print(" 几何平均加速比 %s（标准答案在相同任务上 %s；统计了大数据输出正确的 %d/%d 个任务）"
          % (_fx(gm), _fx(gm_ref), n_valid, len(tasks)))
    print(" “相对标准” = 标准答案耗时 / 候选耗时（>1 表示比标准答案快）；加速比后的 ✗ 表示大数据输出不正确")
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
    fails = [(t, x) for t in tasks for x in c.results[t.key]["tests"] if x["status"] in ("fail", "partial")]
    if c.load_error:
        pass
    elif fails:
        n_part = sum(1 for _, x in fails if x["status"] == "partial")
        print("\n ✗ 未通过的测试（%d 项，其中 ◐ %d 项得一半分）:" % (len(fails), n_part))
        for t, x in fails:
            print("  %s[%s %s] %s" % ("◐ " if x["status"] == "partial" else "", x["id"], x["cat"], x["desc"]))
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
                    print("  ✓ [%s %s] %s（%s）%s" % (x["id"], x["cat"], x["desc"], _ft(x["sec"]),
                                                   ("  " + x["msg"]) if x["msg"] and "耗时" in x["msg"] else ""))
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
    print(" 多模型对比（总分含性能加分）")
    print("═" * 100)
    head = [("候选", 28, False)] + [(t.key, 8, True) for t in tasks] + [("总分", 8, True), ("几何加速", 10, True)]
    print("".join(_pad(h, w, r) + " " for h, w, r in head))
    for c in sorted(cands, key=lambda c: -_summary(c, tasks)[0]):
        total, gm, _, _ = _summary(c, tasks)
        row = [c.label] + ["%.1f" % c.results[t.key]["score"]["total"] for t in tasks] + ["%.1f" % total, _fx(gm)]
        print("".join(_pad(v, w, r) + " " for v, (_h, w, r) in zip(row, head)))


def write_markdown(cands, tasks, path, meta):
    out = ["# AI 代码修复与优化评测报告（v%s 高难度版）" % BENCH_VERSION, "",
           "- Python %s，%s；计时：每个实现 %d 轮取中位数，数据规模系数 %.2f" % (
               sys.version.split()[0], sys.platform, meta["reps"], meta["scale"]),
           "- 计分：每个任务 = 功能 %d + 安全/隐性 %d + 性能 %d + 加分 ≤%d。性能基础分 = %d × ln(加速比)/ln(标准答案加速比)；"
           "加分 = 10 × log2(标准答案耗时/候选耗时/1.1)；二者再乘以功能通过率；安全测试失败时性能分为 0，大数据输出错误时减半且无加分。最坏情况计时测试超时不得分、没超时但结果错误得一半分（◐）。" % (
               W_FUNC, W_HIDDEN, W_PERF, W_BONUS, W_PERF), ""]
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
        out += ["## %s —— 总分 %.1f" % (c.label, total), "",
                "几何平均加速比 **%s**（标准答案在相同任务上 %s；统计了 %d/%d 个大数据输出正确的任务）"
                % (_fx(gm), _fx(gm_ref), n_valid, len(tasks)), "",
                "| 任务 | 功能 | 安全/隐性 | 原代码 | 标准答案 | 候选 | 加速比 | 相对标准 | 性能 | 加分 | 得分 | 备注 |",
                "|---|---|---|---|---|---|---|---|---|---|---|---|"]
        for t in tasks:
            r = c.results[t.key]
            p, s = r["perf"], r["score"]
            fa = [x for x in r["tests"] if x["cat"] == "功能" and x["status"] != "skip"]
            ha = [x for x in r["tests"] if x["cat"] != "功能" and x["status"] != "skip"]
            out.append("| %s %s | %d/%d | %d/%d | %s | %s | %s | %s | %s | %.1f | %.1f | %.1f | %s |" % (
                t.label, t.title, sum(x["status"] == "pass" for x in fa), len(fa),
                sum(x["status"] == "pass" for x in ha), len(ha), _ft(p["base"]), _ft(p["ref"]), _ft(p["cand"]),
                _fx(p["speedup"]), _fx(p["vs_ref"]), s["perf"], s["bonus"], s["total"],
                (p["note"] or "").splitlines()[0].replace("|", "\\|") if p["note"] else ""))
        fails = [x for t in tasks for x in c.results[t.key]["tests"] if x["status"] in ("fail", "partial")]
        if c.load_error:
            out += ["", "### 候选代码无法运行", "", "```text"] + c.load_error.splitlines()[:20] + ["```", ""]
            fails = []
        out += ["", "### 未通过的测试（%d 项，◐ 表示得一半分）" % len(fails), ""]
        for x in fails:
            out += ["- %s**[%s %s] %s**" % ("◐ " if x["status"] == "partial" else "", x["id"], x["cat"], x["desc"]),
                    "", "  ```text"]
            out += ["  " + ln for ln in (x["msg"] or "").splitlines()[:14]]
            out += ["  ```", ""]
        if not fails and not c.load_error:
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
# 第 12 部分：自检（出题官审核自己的标准答案）
# ════════════════════════════════════════════════════════════════════════════

def _crosscheck(rounds=400):
    """标准答案与彼此独立的朴素实现随机对拍（含中等规模数据）。返回不一致的描述列表。"""
    rng = random.Random(20261021)
    bad = []

    def cmp(name, a_fn, b_fn, args, call=None):
        run = (lambda f: _outcome(call, (f, copy.deepcopy(args)))) if call else \
            (lambda f: _outcome(f, copy.deepcopy(args)))
        oa, ob = run(a_fn), run(b_fn)
        same = oa[0] == ob[0] and ((oa[0] == "ok" and _same(oa[1], ob[1])) or
                                   (oa[0] == "exc" and type(oa[1]) is type(ob[1])))
        if not same:
            bad.append("%s 不一致: 输入=%s\n   标准=%s\n   朴素=%s" % (name, _short(args, 300), _short(oa, 300), _short(ob, 300)))

    for _ in range(rounds):
        cmp("T1", _ref_edit_distance, _naive_edit_distance, _rand_t1(rng))
        for _ in range(5):
            cmp("T2", _ref_glob_filter, _naive_glob_filter, _rand_t2(rng))
        cmp("T3", _ref_run_book, _naive_run_book, _rand_t3(rng))
        cmp("T4", _RefTTLCache, _NaiveTTLCache, _rand_t4(rng), call=_cache_call)
        for _ in range(3):
            cmp("T5", _ref_expand, _naive_expand, _rand_t5(rng))
    # 中等规模
    big_rng = random.Random(7)
    for n in (300, 700):
        a = [big_rng.choice("abcdefghij") for _ in range(n)]
        b = [big_rng.choice("abcdefghij") for _ in range(n + 37)]
        cmp("T1(中等)", _ref_edit_distance, _naive_edit_distance, (a, b))
    cmp("T1(中等)", _ref_edit_distance, _naive_edit_distance, _perf_t1(5, 0.4).make())
    cmp("T3(中等)", _ref_run_book, _naive_run_book, (_t3_stream(5, 2500),))
    cmp("T3(中等, 撤单多)", _ref_run_book, _naive_run_book, (_t3_stream(6, 2500, cancel_ratio=0.5, fok_ratio=0.2),))
    cmp("T4(中等)", _RefTTLCache, _NaiveTTLCache, _perf_t4(5, 0.05).make(), call=_cache_call)
    case = _perf_t5(5, 0.1)
    cmp("T5(中等)", _ref_expand, _naive_expand, case.make())
    return bad


def cmd_selftest(args):
    t0 = time.time()
    print("【1/3】标准答案 vs 独立朴素实现，随机对拍 ……", end="", flush=True)
    bad = _crosscheck(400)
    print(" %s" % ("通过" if not bad else "发现 %d 处不一致" % len(bad)))
    for b in bad[:10]:
        print("   ", b)
    scale, reps = (1.0, 3) if args.full else (0.3, 1)
    print("【2/3】把标准答案和原代码当作候选，跑完整评测（性能数据规模 %.1f）……" % scale)
    cands = [load_candidate("@reference"), load_candidate("@baseline")]
    judge(cands, TASKS, scale, reps, args.timeout)
    ref_c, base_c = cands
    print_report(ref_c, TASKS)
    print_report(base_c, TASKS)
    print("【3/3】核对自检结论 ……")
    problems = list(bad)
    for t in TASKS:
        rr, br = ref_c.results[t.key], base_c.results[t.key]
        failed = [x for x in rr["tests"] if x["status"] != "pass"]
        if failed:
            problems.append("%s: 标准答案未通过 %s" % (t.label, ", ".join(x["id"] for x in failed)))
        if not rr["perf"]["valid"]:
            problems.append("%s: 标准答案性能测量异常: %s" % (t.label, rr["perf"]["note"]))
        if rr["perf"]["note"] and "安全" in rr["perf"]["note"]:
            problems.append("%s: %s" % (t.label, rr["perf"]["note"]))
        if (rr["perf"]["ref_speedup"] or 0) < 2:
            problems.append("%s: 标准答案相对原代码的加速不足 2 倍（%s）" % (t.label, _fx(rr["perf"]["ref_speedup"])))
        b_fail = [x for x in br["tests"] if x["status"] != "pass"]
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
    print("✓ 自检通过：标准答案全部测试通过且与朴素实现一致，原代码在每个任务上都被测出问题。")
    return 0


# ════════════════════════════════════════════════════════════════════════════
# 第 13 部分：命令行
# ════════════════════════════════════════════════════════════════════════════

def _select_tasks(only):
    if not only:
        return list(TASKS)
    keys = [k.strip() for k in only.split(",") if k.strip()]
    by_fn = {t.fn.lower(): t for t in TASKS}
    out = []
    for k in keys:
        t = TASK_BY_KEY.get(k.upper()) or by_fn.get(k.lower())
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
    print("AI 代码修复与优化评测 v%s（高难度）| Python %s | 数据规模 ×%.2f | 每个实现计时 %d 轮"
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
    ap = argparse.ArgumentParser(description="AI 代码修复与性能优化评测器 v2（高难度，出题 + 判卷）")
    sub = ap.add_subparsers(dest="cmd")
    p = sub.add_parser("prompt", help="生成发给模型的题目")
    p.add_argument("-o", "--output", help="写入文件（默认打印到屏幕）")
    j = sub.add_parser("judge", help="评测一个或多个候选答案")
    j.add_argument("paths", nargs="+", help="solution.py / 模型完整回复 .md；@baseline、@reference 为内置实现")
    j.add_argument("--quick", action="store_true", help="小规模数据、单轮计时")
    j.add_argument("--reps", type=int, default=0, help="每个实现计时轮数（默认 3）")
    j.add_argument("--scale", type=float, default=0.0, help="性能数据规模系数（默认 1.0）")
    j.add_argument("--only", help="只评测部分任务，如 T1,T3 或 glob_filter")
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
