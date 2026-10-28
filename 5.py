#!/usr/bin/env python3
"""
Bitcoin puzzle range scanner

Files:
  adress.txt : Bitcoin target addresses (one per line, P2PKH addresses starting with 1)
  adress1.txt: Ethereum target addresses (one per line, 0x... hex; optional)
  range.txt  : ranges, scanned in file order (starts from puzzle 71 by default)
               one entry per line:  71   or   400000:7FFFFF   (hex)

Usage:
  python puzzle_scanner.py            -> no address output (default, fastest)
  python puzzle_scanner.py first      -> print only the two pages next to the center point
  python puzzle_scanner.py all        -> print every generated address (very slow)

Note: generated addresses are never written to disk. Only these files are written:
  prefix_matches.txt : first PREFIX_LEN characters matched a target address
  found.txt          : full address match (private key hex + address)
  online_hits.txt    : online hits: BTC with balance > 0 or any history, ETH with balance > 0
  state.json         : progress counters only

How each range is scanned:
  1) Center point = exactly 49.9% of the range:  C = start + size * 499 // 1000
  2) Each page = 128 keys
  3) PAGES_PER_SIDE (default 1,500,000) pages upward from C and the same number
     downward from C, so the 49.9% point sits exactly in the middle of the window
  4) For every key, the Bitcoin addresses (compressed and uncompressed) and the
     Ethereum address are checked against the target files
  5) Progress is saved every CHUNK_PAGES pages; if the program is interrupted
     it resumes from the last saved point

Matches:
  - First PREFIX_LEN (default 8) characters match -> prefix_matches.txt, scanning continues
  - Full address match -> private key hex + address saved to found.txt, program stops
  - Every 5 seconds one key from the window being scanned has its addresses
    (BTC compressed, BTC uncompressed, ETH) checked with the online APIs (separate thread).
    Every checked address is printed with its balance. Written to online_hits.txt:
    BTC with a balance > 0 or any transaction history, ETH with a balance > 0

Install:  pip install coincurve pycryptodome
"""

import hashlib
import json
import multiprocessing as mp
import os
import random
import sys
import threading
import time
import urllib.error
import urllib.request
from bisect import bisect_right
from itertools import islice, zip_longest

from coincurve import PublicKey
from Crypto.Hash import RIPEMD160, keccak

# ------------------------- Settings -------------------------
PAGE_SIZE = 128
PAGES_PER_SIDE = 1_500_000          # pages upward from the center and the same number downward
PCT_NUM, PCT_DEN = 499, 1000        # center point: exactly 49.9% of the range
MAX_STEPS_PER_RANGE = 1             # 1 = only this window; 0 = keep widening until the range edges
CONTINUOUS = True                   # automatically move on to the next range
CHUNK_PAGES = 20_000                # save progress after this many pages
PROGRESS_SECONDS = 30               # print a progress line every N seconds
PREFIX_LEN = 8                      # number of leading characters for a partial match
WORKERS = None                      # None = all CPU cores (single core: no Pool)

ONLINE_CHECK = True                 # online check
ONLINE_INTERVAL = 5                 # one key (two addresses) every N seconds
API_URL = "https://btcbook.guarda.co/api/v2/address/"
ONLINE_TIMEOUT = 10

ETH_ENABLED = True                  # also scan Ethereum addresses
ETH_ADDRESS_FILE = "adress1.txt"    # Ethereum target addresses (0x...), optional file
ETH_RPC_URL = "https://ethereum-rpc.publicnode.com"   # public JSON-RPC used for eth_getBalance
CHECK_BTC_UNCOMPRESSED = True       # False = skip the uncompressed BTC hash (faster)
SHOW_ONLINE_ERRORS = False          # print network/API errors of the online check
ONLINE_DISABLE_AFTER = 5            # switch an online API off after this many errors in a row
SHOW_ONLINE_CHECKED = True          # print every online-checked address with its balance (nothing saved if 0)
SHOW_ONLINE_STATS = False           # print the "Online check so far" line after each range

ADDRESS_FILE = "adress.txt"
RANGE_FILE = "range.txt"
STATE_FILE = "state.json"
FOUND_FILE = "found.txt"
PREFIX_FILE = "prefix_matches.txt"
ONLINE_FILE = "online_hits.txt"

SHOW_MODE = sys.argv[1].lower() if len(sys.argv) > 1 else "none"
# ------------------------------------------------------------

STATE_VERSION = 5
B58 = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"
SECP256K1_N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141


# ---------- Address helpers ----------
def b58_to_int(s: str) -> int:
    n = 0
    for ch in s:
        n = n * 58 + B58.index(ch)
    return n


def b58_to_hash160(addr: str) -> bytes:
    raw = b58_to_int(addr).to_bytes(25, "big")
    if hashlib.sha256(hashlib.sha256(raw[:-4]).digest()).digest()[:4] != raw[-4:]:
        raise ValueError(f"Invalid address: {addr}")
    return raw[1:21]


def hash160(data: bytes) -> bytes:
    return RIPEMD160.new(hashlib.sha256(data).digest()).digest()


def h160_to_addr(h: bytes) -> str:
    payload = b"\x00" + h
    raw = payload + hashlib.sha256(hashlib.sha256(payload).digest()).digest()[:4]
    n = int.from_bytes(raw, "big")
    out = ""
    while n:
        n, r = divmod(n, 58)
        out = B58[r] + out
    pad = len(raw) - len(raw.lstrip(b"\x00"))
    return "1" * pad + out


def key_addresses(k: int):
    """Compressed and uncompressed address of a private key"""
    pub = PublicKey.from_secret(k.to_bytes(32, "big"))
    return (h160_to_addr(hash160(pub.format(compressed=True))),
            h160_to_addr(hash160(pub.format(compressed=False))))


def eth_hash(pub_uncompressed: bytes) -> bytes:
    """20-byte Ethereum address from a 65-byte uncompressed public key"""
    return keccak.new(digest_bits=256, data=pub_uncompressed[1:]).digest()[-20:]


def key_eth_address(k: int) -> str:
    pub = PublicKey.from_secret(k.to_bytes(32, "big"))
    return "0x" + eth_hash(pub.format(compressed=False)).hex()


# ---------- Fast prefix filter ----------
def prefix_intervals(prefix: str):
    """
    Every hash160 whose address starts with `prefix` falls inside a few numeric intervals.
    The real address is only built (and the prefix re-checked) when a hash160 lands
    inside one of these intervals.
    """
    out = []
    for total_len in range(26, 36):
        pad = total_len - len(prefix)
        if pad < 0:
            continue
        lo = b58_to_int(prefix + "1" * pad) >> 32
        hi = b58_to_int(prefix + "z" * pad) >> 32
        if lo >= (1 << 160):
            continue
        out.append((lo, min(hi, (1 << 160) - 1)))
    return out


def merge_intervals(intervals):
    intervals.sort()
    merged = []
    for lo, hi in intervals:
        if merged and lo <= merged[-1][1] + 1:
            merged[-1] = (merged[-1][0], max(merged[-1][1], hi))
        else:
            merged.append((lo, hi))
    return merged


# ---------- Reading input files ----------
def clean_lines(path: str):
    if not os.path.exists(path):
        sys.exit(f"File not found: {path}")
    with open(path, encoding="utf-8") as f:
        for line in f:
            line = line.split("#", 1)[0].strip()
            if line:
                yield line


def load_targets():
    exact = {}          # hash160 -> address
    prefix_map = {}     # prefix -> [addresses]
    for line in clean_lines(ADDRESS_FILE):
        addr = line.split()[0]
        exact[b58_to_hash160(addr)] = addr
        prefix_map.setdefault(addr[:PREFIX_LEN], []).append(addr)
    if not exact:
        sys.exit(f"{ADDRESS_FILE} is empty.")
    intervals = []
    for p in prefix_map:
        intervals.extend(prefix_intervals(p))
    merged = merge_intervals(intervals)
    return (exact, prefix_map, [m[0] for m in merged], [m[1] for m in merged],
            load_eth_targets())


def load_eth_targets():
    """20-byte address -> '0x...' string. None = Ethereum disabled, {} = no targets."""
    if not ETH_ENABLED:
        return None
    eth = {}
    if not os.path.exists(ETH_ADDRESS_FILE):
        print(f"Note: {ETH_ADDRESS_FILE} not found - Ethereum targets skipped "
              f"(the online ETH check still runs).")
        return eth
    for line in clean_lines(ETH_ADDRESS_FILE):
        addr = line.split()[0]
        h = addr[2:] if addr[:2].lower() == "0x" else addr
        try:
            raw = bytes.fromhex(h)
        except ValueError:
            raw = b""
        if len(raw) != 20:
            sys.exit(f"Invalid Ethereum address in {ETH_ADDRESS_FILE}: {addr}")
        eth[raw] = "0x" + h.lower()
    return eth


def parse_range(line: str):
    sep = ":" if ":" in line else ("-" if "-" in line else None)
    if sep is None:
        n = int(line)
        return 1 << (n - 1), (1 << n) - 1
    a, b = line.split(sep, 1)
    start, end = int(a.strip(), 16), int(b.strip(), 16)
    return (start, end) if start <= end else (end, start)


def load_ranges():
    ranges = []
    for line in clean_lines(RANGE_FILE):
        start, end = parse_range(line)
        if start < 1 or end >= SECP256K1_N:
            sys.exit(f"Invalid range: {line}")
        ranges.append((line, start, end))
    if not ranges:
        sys.exit(f"{RANGE_FILE} is empty.")
    return ranges


# ---------- Progress ----------
def load_state():
    if os.path.exists(STATE_FILE):
        with open(STATE_FILE) as f:
            s = json.load(f)
        if s.get("v") == STATE_VERSION:
            return s.get("range_index", 0), s.get("step", 0), s.get("done", 0)
    return 0, 0, 0


def save_state(idx: int, step: int, done: int) -> None:
    tmp = STATE_FILE + ".tmp"
    with open(tmp, "w") as f:
        json.dump({"v": STATE_VERSION, "range_index": idx, "step": step, "done": done}, f)
    os.replace(tmp, STATE_FILE)


# ---------- Pages (streamed, no huge lists) ----------
def center_point(start: int, end: int) -> int:
    """Exactly 49.9% of the range (integer arithmetic)"""
    return start + (end - start + 1) * PCT_NUM // PCT_DEN


def step_layout(start: int, end: int, step: int):
    """Number of pages above and below the center for one step, plus the start index"""
    C = center_point(start, end)
    i0 = step * PAGES_PER_SIDE
    i_max = (step + 1) * PAGES_PER_SIDE - 1
    up_count = max(0, min(i_max, (end - C) // PAGE_SIZE) - i0 + 1)
    down_count = max(0, min(i_max, (C - 1 - start) // PAGE_SIZE) - i0 + 1)
    return C, i0, up_count, down_count


def up_pages(start, end, C, i0, count):
    for i in range(i0, i0 + count):
        first = C + i * PAGE_SIZE
        yield (first, min(first + PAGE_SIZE - 1, end))


def down_pages(start, end, C, i0, count):
    for i in range(i0, i0 + count):
        last = C - i * PAGE_SIZE - 1
        yield (max(last - PAGE_SIZE + 1, start), last)


def interleaved_pages(start, end, C, i0, up_count, down_count):
    """Pages alternate: up, down, up, down ..."""
    for pair in zip_longest(up_pages(start, end, C, i0, up_count),
                            down_pages(start, end, C, i0, down_count)):
        for p in pair:
            if p is not None:
                yield p


def next_state_after(ranges, idx, step):
    start, end = ranges[idx][1], ranges[idx][2]
    _, _, u2, d2 = step_layout(start, end, step + 1)
    finished = (MAX_STEPS_PER_RANGE and step + 1 >= MAX_STEPS_PER_RANGE) or (u2 + d2 == 0)
    return (idx + 1, 0) if finished else (idx, step + 1)


def fmt_duration(sec: float) -> str:
    years = sec / 31557600
    if sec < 60:
        return f"{sec:.0f} sec"
    if sec < 3600:
        return f"{sec / 60:.0f} min"
    if sec < 86400:
        return f"{sec / 3600:.1f} hours"
    if years < 1:
        return f"{sec / 86400:.1f} days"
    return f"{years:.3g} years"


# ---------- Workers ----------
_EXACT = _PREFIX_MAP = _STARTS = _ENDS = _ETH = None
_SHOW_ALL = False


def _init_worker(exact, prefix_map, starts, ends, eth, show_all):
    global _EXACT, _PREFIX_MAP, _STARTS, _ENDS, _ETH, _SHOW_ALL
    _EXACT, _PREFIX_MAP, _STARTS, _ENDS, _ETH, _SHOW_ALL = (
        exact, prefix_map, starts, ends, eth, show_all)


def scan_page(item):
    label, first, last = item
    hits = []
    want_eth = _ETH is not None and (bool(_ETH) or _SHOW_ALL)
    want_unc = CHECK_BTC_UNCOMPRESSED or _SHOW_ALL
    for k in range(first, last + 1):
        pub = PublicKey.from_secret(k.to_bytes(32, "big"))
        pu = pub.format(compressed=False) if (want_unc or want_eth) else None
        hc = hash160(pub.format(compressed=True))
        hu = hash160(pu) if want_unc else None
        he = eth_hash(pu) if want_eth else None

        if _SHOW_ALL:
            print(f"{k:x} {h160_to_addr(hc)} {h160_to_addr(hu)} 0x{he.hex()}", flush=True)

        if he is not None and he in _ETH:
            return [("EXACT", label, k, _ETH[he], _ETH[he], "ethereum")]

        for atype, h in (("compressed", hc), ("uncompressed", hu)):
            if h is None:
                continue
            if h in _EXACT:
                return [("EXACT", label, k, _EXACT[h], _EXACT[h], atype)]

            hv = int.from_bytes(h, "big")
            i = bisect_right(_STARTS, hv) - 1
            if i >= 0 and hv <= _ENDS[i]:              # fast filter
                addr = h160_to_addr(h)
                targets = _PREFIX_MAP.get(addr[:PREFIX_LEN])
                if targets:
                    hits.append(("PREFIX", label, k, addr, ",".join(targets), atype))
    return hits


# ---------- Online check ----------
ONLINE_STATS = {"checked": 0, "errors": 0, "hits": 0}


def fetch_address(addr: str):
    req = urllib.request.Request(
        API_URL + addr,
        headers={"User-Agent": "Mozilla/5.0", "Accept": "application/json"},
    )
    with urllib.request.urlopen(req, timeout=ONLINE_TIMEOUT) as resp:
        return json.loads(resp.read().decode("utf-8"))


def _int(x) -> int:
    try:
        return int(x)
    except (TypeError, ValueError):
        return 0


def eth_rpc(method: str, addr: str) -> int:
    body = json.dumps({"jsonrpc": "2.0", "id": 1, "method": method,
                       "params": [addr, "latest"]}).encode()
    req = urllib.request.Request(
        ETH_RPC_URL, data=body,
        headers={"User-Agent": "Mozilla/5.0", "Content-Type": "application/json"},
    )
    with urllib.request.urlopen(req, timeout=ONLINE_TIMEOUT) as resp:
        data = json.loads(resp.read().decode("utf-8"))
    if "result" not in data:
        raise RuntimeError(str(data.get("error")))
    return int(data["result"], 16)


def eth_balance_wei(addr: str) -> int:
    return eth_rpc("eth_getBalance", addr)


ONLINE_STATE = {"btc": {"on": True, "fail": 0}, "eth": {"on": True, "fail": 0}}


def _service_ok(name: str) -> None:
    ONLINE_STATE[name]["fail"] = 0


def _service_fail(name: str, addr: str, e: Exception) -> None:
    """Count an error; switch the API off for the rest of the run if it looks blocked."""
    ONLINE_STATS["errors"] += 1
    st = ONLINE_STATE[name]
    st["fail"] += 1
    if SHOW_ONLINE_ERRORS:
        print(f"  [online] error checking {addr}: {e}", flush=True)
    blocked = isinstance(e, urllib.error.HTTPError) and e.code in (403, 429)
    if st["on"] and (blocked or st["fail"] >= ONLINE_DISABLE_AFTER):
        st["on"] = False
        why = "blocked / rate limited" if blocked else f"{st['fail']} errors in a row"
        print(f"  [online] {name.upper()} online check switched off ({why}). "
              f"Scanning continues.", flush=True)


def _online_hit(msg: str, has_funds: bool = True) -> None:
    ONLINE_STATS["hits"] += 1
    print("Online balance found:" if has_funds else "Online history found:", msg, flush=True)
    with open(ONLINE_FILE, "a", encoding="utf-8") as f:
        f.write(msg + "\n")


def online_check_key(k: int, label: str):
    if ONLINE_STATE["btc"]["on"]:
        comp, uncomp = key_addresses(k)
        for kind, addr in (("BTC compressed", comp), ("BTC uncompressed", uncomp)):
            if not ONLINE_STATE["btc"]["on"]:
                break
            try:
                info = fetch_address(addr)
            except Exception as e:
                _service_fail("btc", addr, e)
                continue
            _service_ok("btc")
            ONLINE_STATS["checked"] += 1
            bal = _int(info.get("balance"))
            txs = _int(info.get("txs")) + _int(info.get("unconfirmedTxs"))
            received = _int(info.get("totalReceived"))
            if bal > 0 or txs > 0 or received > 0:      # balance OR any history -> save
                _online_hit(f"range [{label}] | key {k:064x} | {kind} | address {addr} | "
                            f"balance {bal} sat | txs {txs} | total received {received}",
                            has_funds=bal > 0)
            elif SHOW_ONLINE_CHECKED:
                print(f"  [online] {kind} {addr} | balance: 0 | txs: 0", flush=True)

    if ETH_ENABLED and ONLINE_STATE["eth"]["on"]:
        addr = key_eth_address(k)
        try:
            wei = eth_balance_wei(addr)                 # one request per address
        except Exception as e:
            _service_fail("eth", addr, e)
            return
        _service_ok("eth")
        ONLINE_STATS["checked"] += 1
        if wei > 0:                                     # balance > 0 -> save
            _online_hit(f"range [{label}] | key {k:064x} | ETH | address {addr} | "
                        f"balance {wei / 10**18:.8f} ETH")
        elif SHOW_ONLINE_CHECKED:
            print(f"  [online] ETH {addr} | balance: 0", flush=True)


def online_sampler(progress, stop_event):
    """Every ONLINE_INTERVAL seconds, check one key from the current page online (both addresses)."""
    while not stop_event.wait(ONLINE_INTERVAL):
        if not (ONLINE_STATE["btc"]["on"] or (ETH_ENABLED and ONLINE_STATE["eth"]["on"])):
            break                                   # every online API is off: stop the thread
        item = progress.get("item")
        if item is None:
            continue
        label, first, last = item
        try:
            online_check_key(random.randint(first, last), label)
        except Exception:
            ONLINE_STATS["errors"] += 1


# ---------- Running ----------
def show_page(title, first, last):
    print(f"--- {title} ({last - first + 1} keys) ---")
    print("key(hex)  compressed_address  uncompressed_address  ethereum_address")
    for k in range(first, last + 1):
        comp, uncomp = key_addresses(k)
        eth = key_eth_address(k) if ETH_ENABLED else "-"
        print(f"{k:x} {comp} {uncomp} {eth}")


def run_step(targets, ranges, idx, step, done0, launch_stats):
    """One step (window) of one range, with progress saving. Returns ('stop'|'ok', next_state)"""
    exact, prefix_map, starts, ends, eth = targets
    label, start, end = ranges[idx]
    C, i0, up_count, down_count = step_layout(start, end, step)
    total = up_count + down_count
    nxt_idx, nxt_step = next_state_after(ranges, idx, step)

    if total == 0 or done0 >= total:
        save_state(nxt_idx, nxt_step, 0)
        return "ok", (nxt_idx, nxt_step, 0)

    low = max(start, C - (i0 + down_count) * PAGE_SIZE)
    high = min(end, C + (i0 + up_count) * PAGE_SIZE - 1)
    print(f"\n=== Range [{label}] | step {step + 1} ===")
    print(f"Center point (49.9%): {C:x}")
    print(f"Window: {low:x} to {high:x}")
    print(f"{down_count:,} pages below + {up_count:,} pages above = {total:,} pages "
          f"({total * PAGE_SIZE:,} keys)"
          + (f" | resuming from page {done0:,}" if done0 else ""))

    if SHOW_MODE == "first" and done0 == 0:
        if down_count:
            show_page("First page below the center point", *next(down_pages(start, end, C, i0, 1)))
        if up_count:
            show_page("First page above the center point", *next(up_pages(start, end, C, i0, 1)))

    workers = WORKERS or os.cpu_count() or 1
    initargs = (exact, prefix_map, starts, ends, eth, SHOW_MODE == "all")
    pool = None
    if workers == 1:
        _init_worker(*initargs)                     # single core: no Pool
    else:
        pool = mp.Pool(workers, initializer=_init_worker, initargs=initargs)

    progress = {"item": None}
    stop_event = threading.Event()
    if ONLINE_CHECK:
        threading.Thread(target=online_sampler, args=(progress, stop_event),
                         daemon=True).start()

    pages = islice(interleaved_pages(start, end, C, i0, up_count, down_count),
                   done0, None)
    done = done0
    stopped = False
    last_print = time.time()

    try:
        while not stopped:
            chunk = [(label, a, b) for a, b in islice(pages, CHUNK_PAGES)]
            if not chunk:
                break
            progress["item"] = chunk[0]
            results = (pool.imap_unordered(scan_page, chunk, chunksize=16)
                       if pool else map(scan_page, chunk))

            for j, hits in enumerate(results):
                progress["item"] = chunk[min(j, len(chunk) - 1)]
                for kind, lb, k, addr, tgt, atype in hits:
                    if kind == "EXACT":
                        msg = (f"FULL MATCH! range [{lb}] | address ({atype}): {addr} | "
                               f"private key (hex): {k:064x}")
                        print(msg, flush=True)
                        with open(FOUND_FILE, "a", encoding="utf-8") as f:
                            f.write(msg + "\n")
                        stopped = True
                    else:
                        msg = (f"range [{lb}] | key {k:064x} | address ({atype}) {addr} | "
                               f"target {tgt}")
                        print("Prefix match:", msg, flush=True)
                        with open(PREFIX_FILE, "a", encoding="utf-8") as f:
                            f.write(msg + "\n")
                if stopped:
                    break

                launch_stats["pages"] += 1
                now = time.time()
                if now - last_print >= PROGRESS_SECONDS:
                    last_print = now
                    rate = launch_stats["pages"] * PAGE_SIZE / (now - launch_stats["t0"])
                    left = (total - (done + j + 1)) * PAGE_SIZE
                    print(f"  {done + j + 1:,}/{total:,} pages "
                          f"({(done + j + 1) / total * 100:.1f}%) | {rate:,.0f} keys/sec | "
                          f"remaining for this range: {fmt_duration(left / rate)}", flush=True)

            if stopped:
                break
            done += len(chunk)
            save_state(idx, step, done)             # save progress after every chunk
    finally:
        stop_event.set()
        if pool is not None:
            pool.terminate()

    if stopped:
        print("Search stopped (full match).")
        return "stop", (idx, step, done)

    save_state(nxt_idx, nxt_step, 0)
    rate = launch_stats["pages"] * PAGE_SIZE / (time.time() - launch_stats["t0"])
    print(f"Finished range [{label}] | average {rate:,.0f} keys/sec.")
    if ONLINE_CHECK and SHOW_ONLINE_STATS:
        print(f"Online check so far: {ONLINE_STATS['checked']} addresses checked, "
              f"{ONLINE_STATS['errors']} errors, {ONLINE_STATS['hits']} with balance")
    remaining = len(ranges) - nxt_idx
    if remaining > 0 and MAX_STEPS_PER_RANGE:
        eta = remaining * MAX_STEPS_PER_RANGE * total * PAGE_SIZE / rate
        print(f"Ranges remaining: {remaining} | estimated time to finish all: {fmt_duration(eta)}")
    return "ok", (nxt_idx, nxt_step, 0)


def main():
    if SHOW_MODE not in ("first", "all", "none"):
        sys.exit("Display mode must be first, all or none.")

    targets = load_targets()
    ranges = load_ranges()
    idx, step, done = load_state()

    if idx >= len(ranges):
        print("All ranges are finished. Delete state.json to start over.")
        return

    launch_stats = {"pages": 0, "t0": time.time()}
    while idx < len(ranges):
        status, (idx, step, done) = run_step(targets, ranges, idx, step, done, launch_stats)
        if status == "stop" or not CONTINUOUS:
            break

    if idx >= len(ranges):
        print("All ranges are finished.")
    else:
        print(f"Next run will continue from range [{ranges[idx][0]}].")


if __name__ == "__main__":
    main()
