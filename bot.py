import os
import re
import json
import time
import smtplib
from email.message import EmailMessage
import math
import html
import bisect
import datetime as dt
from collections import defaultdict
from concurrent.futures import ThreadPoolExecutor

import requests

TR = dt.timezone(dt.timedelta(hours=3))
UTC = dt.timezone.utc
BASE = "https://site.api.espn.com/apis/site/v2/sports/soccer/{slug}/scoreboard"

# (ESPN kodu, görünen ad, takvim yılı sezonu mu?)
LEAGUES = [
    ("eng.1", "İngiltere Premier Lig", False),
    ("esp.1", "İspanya La Liga", False),
    ("ita.1", "İtalya Serie A", False),
    ("ger.1", "Almanya Bundesliga", False),
    ("fra.1", "Fransa Ligue 1", False),
    ("ger.2", "Almanya 2. Lig", False),
    ("usa.1", "ABD MLS", True),
    ("bra.1", "Brezilya 1. Lig", True),
    ("swe.1", "İsveç 1. Lig", True),
    ("nor.1", "Norveç 1. Lig", True),
    ("den.1", "Danimarka 1. Lig", False),
    ("sco.1", "İskoçya 1. Lig", False),
    ("fra.2", "Fransa 2. Lig", False),
]

HISTORY_DAYS = 420      # geçmiş veri penceresi
HALF_LIFE = 100         # gün: zaman ağırlığı yarı ömrü
LAST_N = 10             # takımın son N maçı
BOOST = 1.5             # son N maça ek ağırlık çarpanı
PRIOR = 5.0             # az maçı olan takımı lige çeken "sanal maç" sayısı
HT_PRIOR = 8.0          # ilk yarı payında lig ortalamasına çeken "sanal gol" sayısı
NEW_ATT, NEW_DEF = 0.85, 1.15   # verisi olmayan (yeni çıkan) takım varsayımı
LOW_DATA = 5            # bundan az maçı olan takım "az veri" uyarısı alır
DAY_START = 6           # iddaa günü: 06:00 - ertesi gün 06:00 (TR)
BACKTEST_DAYS = 60      # doğruluk tablosunun ölçtüğü son gün sayısı
CALIB_DAYS = 90         # bunun öncesindeki günler ayar (kalibrasyon) için kullanılır
MIN_CALIB = 150         # ligin kendi ayarı için gereken en az maç; azsa tüm liglerin ortak ayarı
RHO_GRID = [x / 100 for x in range(-25, 11)]
SIM_K = 60              # skor ve sürpriz karşılaştırması için en benzer geçmiş maç sayısı
VALUE_MIN_EV = 0.05     # değerli oran: beklenen getiri en az %5
VALUE_MAX_EV = 0.40     # bunun üstü genelde model hatasıdır, gösterilmez
VALUE_MIN_P = 0.25      # çok düşük olasılıklı oranlar değerli sayılmaz
SURPRISE_MIN_P = 0.035  # sürpriz radarı (2/1, 1/2) için en düşük model olasılığı
STORE = "data/tahminler.json"
KEEP_DAYS = 180
CONF = 0.65             # karnede "güçlü tahmin" eşiği


# ---------------------------------------------------------------- veri çekme
HEADERS = {
    "User-Agent": ("Mozilla/5.0 (iPhone; CPU iPhone OS 17_0 like Mac OS X) "
                   "AppleWebKit/605.1.15 (KHTML, like Gecko) Version/17.0 "
                   "Mobile/15E148 Safari/604.1"),
    "Accept": "application/json",
}


class Rejected(Exception):
    pass


def http_json(url, params):
    last = "bilinmiyor"
    params = dict(params)
    for _ in range(3):
        r = None
        try:
            r = requests.get(url, params=params, headers=HEADERS, timeout=30)
            if r.status_code == 400 and "limit" in params:
                params.pop("limit")
                continue
            if 400 <= r.status_code < 500 and r.status_code != 429:
                raise Rejected(f"HTTP {r.status_code} {r.text[:80]}")
            r.raise_for_status()
            return r.json()
        except Rejected:
            raise
        except requests.HTTPError:
            last = f"HTTP {r.status_code} {r.text[:80]}"
        except Exception as e:  # noqa
            last = f"{type(e).__name__} {str(e)[:80]}"
        time.sleep(2)
    raise RuntimeError(last)


def first_half(d):
    """Gol ilk yarıda mı? '33'', '45'+3'' gibi dakika yazısından çıkarır."""
    clk = d.get("clock") or {}
    mt = re.match(r"\s*(\d+)", str(clk.get("displayValue") or ""))
    if mt:
        return int(mt.group(1)) <= 45
    v = clk.get("value")
    if v is None:
        return None
    return float(v) <= 2700


def ht_score(comp, hid, aid, hg, ag):
    """Gol olaylarından ilk yarı skorunu çıkarır. Emin olamazsa None döner."""
    if hg is None or ag is None:
        return None
    if hg + ag == 0:
        return (0, 0)
    det = comp.get("details")
    if not det:
        return None
    goals = [d for d in det if d.get("scoringPlay") and not d.get("shootout")]
    # Kendi kalesine gollerin hangi takıma yazıldığı belirsiz: iki yorumu da dene,
    # maç sonu skoruyla tutanı kullan.
    for flip in (False, True):
        cnt = {hid: [0, 0], aid: [0, 0]}
        ok = True
        for d in goals:
            tid = str((d.get("team") or {}).get("id", ""))
            if flip and d.get("ownGoal"):
                tid = aid if tid == hid else (hid if tid == aid else tid)
            fh = first_half(d)
            if tid not in cnt or fh is None:
                ok = False
                break
            cnt[tid][0] += 1
            cnt[tid][1] += 1 if fh else 0
        if ok and cnt[hid][0] == hg and cnt[aid][0] == ag:
            return cnt[hid][1], cnt[aid][1]
    return None


def am_to_dec(v):
    """Amerikan oranı (+175 / -165) -> ondalık oran (2.75 / 1.61)."""
    if v is None:
        return None
    s = str(v).strip().upper()
    if s in ("EVEN", "EV"):
        return 2.0
    try:
        x = float(s.replace("+", ""))
    except ValueError:
        return None
    if x >= 100:
        return round(1 + x / 100, 3)
    if x <= -100:
        return round(1 + 100 / -x, 3)
    return None


def pick(d, *path):
    for k in path:
        if not isinstance(d, dict):
            return None
        d = d.get(k)
    return d


def parse_odds(comp):
    lst = comp.get("odds") or []
    if not lst or not isinstance(lst[0], dict):
        return None
    o = lst[0]
    res = {}
    for when in ("close", "open"):
        h = am_to_dec(pick(o, "moneyline", "home", when, "odds"))
        d = am_to_dec(pick(o, "moneyline", "draw", when, "odds"))
        a = am_to_dec(pick(o, "moneyline", "away", when, "odds"))
        if h and d and a:
            res.update({"1": h, "X": d, "2": a})
            break
    if "1" not in res:
        h = am_to_dec(pick(o, "homeTeamOdds", "moneyLine"))
        d = am_to_dec(pick(o, "drawOdds", "moneyLine"))
        a = am_to_dec(pick(o, "awayTeamOdds", "moneyLine"))
        if h and d and a:
            res.update({"1": h, "X": d, "2": a})
    for when in ("close", "open"):
        line = pick(o, "total", "over", when, "line")
        ov = am_to_dec(pick(o, "total", "over", when, "odds"))
        un = am_to_dec(pick(o, "total", "under", when, "odds"))
        try:
            ln = float(str(line).lstrip("ouOU")) if line else None
        except ValueError:
            ln = None
        if ln and ov and un:
            res.update({"line": ln, "over": ov, "under": un})
            break
    if res:
        res["src"] = pick(o, "provider", "name") or ""
    return res or None


def parse_event(ev):
    comp = ev["competitions"][0]
    home = away = None
    for c in comp["competitors"]:
        if c.get("homeAway") == "home":
            home = c
        else:
            away = c
    if not home or not away:
        return None
    st = ev.get("status", {}).get("type", {})

    def score(c):
        try:
            return int(c.get("score"))
        except (TypeError, ValueError):
            return None

    def name(c):
        t = c["team"]
        return t.get("shortDisplayName") or t.get("displayName") or t.get("name")

    date = dt.datetime.fromisoformat(ev["date"].replace("Z", "+00:00"))
    if date.tzinfo is None:
        date = date.replace(tzinfo=UTC)
    done = bool(st.get("completed"))
    hid, aid = str(home["team"]["id"]), str(away["team"]["id"])
    hg, ag = score(home), score(away)
    return {
        "id": ev["id"], "date": date, "hid": hid, "aid": aid,
        "home": name(home), "away": name(away), "hg": hg, "ag": ag,
        "ht": ht_score(comp, hid, aid, hg, ag) if done else None,
        "odds": parse_odds(comp),
        "done": done, "state": st.get("state", ""),
    }


def get_chunk(slug, d1, d2):
    dates = f"{d1:%Y%m%d}" if d1 == d2 else f"{d1:%Y%m%d}-{d2:%Y%m%d}"
    params = {"dates": dates}
    if d1 != d2:
        params["limit"] = 500
    data = http_json(BASE.format(slug=slug), params)
    out = []
    for ev in data.get("events", []):
        try:
            m = parse_event(ev)
        except Exception:  # noqa
            m = None
        if m:
            out.append(m)
    return out


def make_chunks(start, end, size):
    res, d = [], start
    while d <= end:
        d2 = min(d + dt.timedelta(days=size - 1), end)
        res.append((d, d2))
        d = d2 + dt.timedelta(days=1)
    return res


def fetch_league(slug, now):
    """Son günlerin tüm maçları. ESPN'in kabul ettiği aralık boyutunu kendisi bulur."""
    end = now.date() + dt.timedelta(days=1)
    probe_err = ""
    for size in (45, 21, 7, 1):
        days = HISTORY_DAYS if size > 1 else 330
        start = now.date() - dt.timedelta(days=days)
        chunks = make_chunks(start, end, size)
        try:
            first = get_chunk(slug, *chunks[-2])
        except Exception as e:  # noqa
            probe_err += f" [{size}g: {e}]"
            continue
        events = {m["id"]: m for m in first}
        fails = 0
        with ThreadPoolExecutor(max_workers=8) as ex:
            futs = [ex.submit(get_chunk, slug, d1, d2) for d1, d2 in chunks]
            for f in futs:
                try:
                    for m in f.result():
                        events[m["id"]] = m
                except Exception:  # noqa
                    fails += 1
        print(f"  {slug}: aralık {size} gün, {len(chunks)} istek, {fails} hata, {len(events)} maç",
              flush=True)
        allm = sorted(events.values(), key=lambda m: m["date"])
        finished = [m for m in allm if m["done"] and m["hg"] is not None and m["ag"] is not None]
        if len(finished) < 30 and size > 1:      # bazı ligler aralık sorgusuna boş döner
            probe_err += f" [{size}g: {len(finished)} maç]"
            continue
        return finished, allm
    raise RuntimeError(probe_err or "hiçbir aralık kabul edilmedi")


# --------------------------------------------------------------------- model
def time_weights(matches, ref):
    return [0.5 ** (max((ref - m["date"]).days, 0) / HALF_LIFE) for m in matches]


def fit_strength(matches, tw):
    """Zaman ağırlıklı + son-10 vurgulu, rakip gücüne göre düzeltilmiş hücum/savunma."""
    n = len(matches)
    byteam = defaultdict(list)
    for i, m in enumerate(matches):
        byteam[m["hid"]].append(i)
        byteam[m["aid"]].append(i)
    recent = set()
    for t, idx in byteam.items():
        for i in idx[-LAST_N:]:
            recent.add((t, i))
    wh = [tw[i] * (BOOST if (matches[i]["hid"], i) in recent else 1.0) for i in range(n)]
    wa = [tw[i] * (BOOST if (matches[i]["aid"], i) in recent else 1.0) for i in range(n)]

    sw = sum(tw)
    lg_h = max(sum(tw[i] * matches[i]["hg"] for i in range(n)) / sw, 0.2)
    lg_a = max(sum(tw[i] * matches[i]["ag"] for i in range(n)) / sw, 0.2)
    base = math.sqrt(lg_h * lg_a)
    ha = math.sqrt(lg_h / lg_a)

    att = {t: 1.0 for t in byteam}
    dfn = {t: 1.0 for t in byteam}
    c = PRIOR * base
    for _ in range(10):
        na, da, nd, dd = (defaultdict(float) for _ in range(4))
        for i, m in enumerate(matches):
            h, a = m["hid"], m["aid"]
            w1, w2 = wh[i], wa[i]
            na[h] += w1 * m["hg"]
            da[h] += w1 * base * ha * dfn[a]
            na[a] += w2 * m["ag"]
            da[a] += w2 * base / ha * dfn[h]
            nd[h] += w1 * m["ag"]
            dd[h] += w1 * base / ha * att[a]
            nd[a] += w2 * m["hg"]
            dd[a] += w2 * base * ha * att[h]
        att = {t: (na[t] + c) / (da[t] + c) for t in att}
        dfn = {t: (nd[t] + c) / (dd[t] + c) for t in dfn}
        ma = sum(att.values()) / len(att)
        md = sum(dfn.values()) / len(dfn)
        att = {t: v / ma for t, v in att.items()}
        dfn = {t: v / md for t, v in dfn.items()}
    games = {t: len(idx) for t, idx in byteam.items()}
    return {"att": att, "dfn": dfn, "base": base, "ha": ha, "games": games, "rho": 0.0}


def tau(i, j, lh, la, rho):
    """Dixon-Coles düzeltmesi: 0-0, 1-0, 0-1, 1-1 skorlarının olasılığını ayarlar."""
    if i == 0 and j == 0:
        return 1 - lh * la * rho
    if i == 0 and j == 1:
        return 1 + lh * rho
    if i == 1 and j == 0:
        return 1 + la * rho
    if i == 1 and j == 1:
        return 1 - rho
    return 1.0


def fit_rho(matches, tw, model):
    terms = []
    for m, w in zip(matches, tw):
        if m["hg"] <= 1 and m["ag"] <= 1:
            lam = lambdas(model, m["hid"], m["aid"])
            terms.append((m["hg"], m["ag"], lam[0], lam[1], w))
    best, best_ll = 0.0, -1e18
    for rho in RHO_GRID:
        ll = 0.0
        for i, j, lh, la, w in terms:
            t = tau(i, j, lh, la, rho)
            if t <= 0:
                ll = -1e18
                break
            ll += w * math.log(t)
        if ll > best_ll:
            best, best_ll = rho, ll
    return best


def fit_half(matches, tw):
    """Lig ve takım bazında gollerin ne kadarının ilk yarıda geldiği."""
    rows = [(m, w) for m, w in zip(matches, tw) if m.get("ht")]
    if len(rows) < 30:
        return None
    g1 = sum(w * (m["ht"][0] + m["ht"][1]) for m, w in rows)
    g = sum(w * (m["hg"] + m["ag"]) for m, w in rows)
    if g <= 0:
        return None
    f = g1 / g
    sf1, sf, cf1, cf = (defaultdict(float) for _ in range(4))
    for m, w in rows:
        h, a = m["hid"], m["aid"]
        sf1[h] += w * m["ht"][0]
        sf[h] += w * m["hg"]
        cf1[h] += w * m["ht"][1]
        cf[h] += w * m["ag"]
        sf1[a] += w * m["ht"][1]
        sf[a] += w * m["ag"]
        cf1[a] += w * m["ht"][0]
        cf[a] += w * m["hg"]
    teams = set(sf) | set(cf)
    a_sh = {t: (sf1[t] + HT_PRIOR * f) / (sf[t] + HT_PRIOR) for t in teams}
    d_sh = {t: (cf1[t] + HT_PRIOR * f) / (cf[t] + HT_PRIOR) for t in teams}
    return {"f": f, "as": a_sh, "ds": d_sh, "cov": len(rows) / len(matches)}


def build_model(matches, ref):
    if len(matches) < 30:
        return None
    tw = time_weights(matches, ref)
    model = fit_strength(matches, tw)
    model["rho"] = fit_rho(matches, tw, model)
    model["half"] = fit_half(matches, tw)
    return model


def lambdas(model, h, a):
    if not model:
        return None
    att, dfn = model["att"], model["dfn"]
    b, ha = model["base"], model["ha"]
    lam_h = b * ha * att.get(h, NEW_ATT) * dfn.get(a, NEW_DEF)
    lam_a = b / ha * att.get(a, NEW_ATT) * dfn.get(h, NEW_DEF)
    return min(max(lam_h, 0.15), 5.0), min(max(lam_a, 0.15), 5.0)


def half_lams(model, h, a, lam_h, lam_a):
    hm = model.get("half") if model else None
    if not hm:
        return None
    f = hm["f"]
    sh = (hm["as"].get(h, f) + hm["ds"].get(a, f)) / 2
    sa = (hm["as"].get(a, f) + hm["ds"].get(h, f)) / 2
    sh, sa = min(max(sh, 0.25), 0.65), min(max(sa, 0.25), 0.65)
    return lam_h * sh, lam_a * sa


K_GRID = [x / 20 for x in range(6, 21)]          # 0.30 .. 1.00
C_GRID = [x / 100 for x in range(80, 131, 2)]     # 0.80 .. 1.30


def mus(model):
    return model["base"] * model["ha"], model["base"] / model["ha"]


def calibrate(lam, mu, kc):
    """Ham beklenen golü düzeltir: k<1 uç tahminleri lig ortalamasına çeker, c genel gol seviyesini ayarlar."""
    k, c = kc
    return tuple(min(max(c * m * (l / m) ** k, 0.15), 5.0) for l, m in zip(lam, mu))


def fit_kc(rows):
    """Geçmiş tahminlerin gerçek gollere en iyi uyduğu (k, c) ayarını bulur."""
    if len(rows) < 120:
        return (0.8, 1.0)
    best, best_ll = (1.0, 1.0), -1e18
    for k in K_GRID:
        for c in C_GRID:
            ll = 0.0
            for r in rows:
                lh, la = calibrate(r["lam"], r["mu"], (k, c))
                ll += r["hg"] * math.log(lh) - lh + r["ag"] * math.log(la) - la
            if ll > best_ll:
                best, best_ll = (k, c), ll
    return best


def pois(k, lam):
    return math.exp(-lam) * lam ** k / math.factorial(k)


def res3(i, j):
    return 0 if i > j else (1 if i == j else 2)


def analyze(lam_h, lam_a, rho=0.0, half=None, joint=True):
    N = 10
    ph = [pois(k, lam_h) for k in range(N)]
    pa = [pois(k, lam_a) for k in range(N)]
    grid = {(i, j): ph[i] * pa[j] * tau(i, j, lam_h, lam_a, rho)
            for i in range(N) for j in range(N)}
    tot = sum(grid.values())
    grid = {k: v / tot for k, v in grid.items()}

    def S(f):
        return sum(p for (i, j), p in grid.items() if f(i, j))

    r = {
        "p1": S(lambda i, j: i > j), "px": S(lambda i, j: i == j), "p2": S(lambda i, j: i < j),
        "o15": S(lambda i, j: i + j >= 2), "o25": S(lambda i, j: i + j >= 3),
        "o35": S(lambda i, j: i + j >= 4),
        "btts": S(lambda i, j: i >= 1 and j >= 1),
        "h05": S(lambda i, j: i >= 1), "a05": S(lambda i, j: j >= 1),
        "h15": S(lambda i, j: i >= 2), "a15": S(lambda i, j: j >= 2),
        "tg": (S(lambda i, j: i + j <= 1), S(lambda i, j: 2 <= i + j <= 3),
               S(lambda i, j: 4 <= i + j <= 5), S(lambda i, j: i + j >= 6)),
        "top": [(f"{i}-{j}", p) for (i, j), p in sorted(grid.items(), key=lambda x: -x[1])[:3]],
        "scores": {f"{i}-{j}": p for (i, j), p in grid.items()},
        "lam1": None,
    }
    if not half:
        return r

    l1h, l1a = half
    l2h, l2a = max(lam_h - l1h, 0.05), max(lam_a - l1a, 0.05)
    M = 7

    def hgrid(x, y):
        qx = [pois(k, x) for k in range(M)]
        qy = [pois(k, y) for k in range(M)]
        g = {(i, j): qx[i] * qy[j] for i in range(M) for j in range(M)}
        t = sum(g.values())
        return {k: v / t for k, v in g.items()}

    g1, g2 = hgrid(l1h, l1a), hgrid(l2h, l2a)
    r["lam1"] = (l1h, l1a)
    r["iy05"] = 1 - g1[(0, 0)]
    r["iy15"] = sum(p for (i, j), p in g1.items() if i + j >= 2)
    r["iykg"] = sum(p for (i, j), p in g1.items() if i >= 1 and j >= 1)
    r["iy1"] = sum(p for (i, j), p in g1.items() if i > j)
    r["iyx"] = sum(p for (i, j), p in g1.items() if i == j)
    r["iy2"] = sum(p for (i, j), p in g1.items() if i < j)
    r["y2_05"] = 1 - g2[(0, 0)]
    r["y2_15"] = sum(p for (i, j), p in g2.items() if i + j >= 2)
    if joint:
        cells = defaultdict(float)
        more = [0.0, 0.0, 0.0]          # 1. yarı / 2. yarı / eşit
        for (i1, j1), p1 in g1.items():
            ht = res3(i1, j1)
            for (i2, j2), p2 in g2.items():
                p = p1 * p2
                cells[(ht, res3(i1 + i2, j1 + j2))] += p
                t1, t2 = i1 + j1, i2 + j2
                more[0 if t1 > t2 else (1 if t1 < t2 else 2)] += p
        ft = [r["p1"], r["px"], r["p2"]]
        for k in range(3):              # İY/MS'yi ana MS olasılıklarıyla tutarlı yap
            s = sum(cells[(h, k)] for h in range(3))
            if s > 0:
                for h in range(3):
                    cells[(h, k)] *= ft[k] / s
        r["htft"] = dict(cells)
        r["more"] = more
        r["p21"] = cells[(2, 0)]       # İY deplasman önde, MS ev sahibi kazanır
        r["p12"] = cells[(0, 2)]       # İY ev sahibi önde, MS deplasman kazanır
    return r


def neighbors(past_lams, lam_h, lam_a, k=SIM_K):
    """Beklenen gol profili bugünkü maça en yakın k geçmiş maç."""
    sc = sorted(past_lams, key=lambda x: (x[0][0] - lam_h) ** 2 + (x[0][1] - lam_a) ** 2)
    return [m for _, m in sc[:k]]


def sim_text(m):
    ht = f" (İY {m['ht'][0]}-{m['ht'][1]})" if m.get("ht") else ""
    return f"{m['date']:%d.%m.%Y} {m['home']} {m['hg']}-{m['ag']} {m['away']}{ht}"


def sim_stats(nb):
    """Komşu maçlarda skor sıklığı ve İY/MS tersine dönüşleri."""
    cnt = defaultdict(int)
    for m in nb:
        cnt[f"{m['hg']}-{m['ag']}"] += 1
    hts = [m for m in nb if m.get("ht")]
    r21 = sum(1 for m in hts if m["ht"][0] < m["ht"][1] and m["hg"] > m["ag"])
    r12 = sum(1 for m in hts if m["ht"][0] > m["ht"][1] and m["hg"] < m["ag"])
    return {"n": len(nb), "scores": dict(cnt), "nht": len(hts), "r21": r21, "r12": r12}


# ------------------------------------------------------------ değerli oran
LINE_KEY = {1.5: "o15", 2.5: "o25", 3.5: "o35"}


def market_list(r, odds):
    """(etiket, kod, model olasılığı, oran, piyasa olasılığı) listesi."""
    out = []
    if not odds:
        return out
    if "1" in odds:
        inv = [1 / odds["1"], 1 / odds["X"], 1 / odds["2"]]
        t = sum(inv)
        for lab, code, p, o, q in (("MS 1", "1", r["p1"], odds["1"], inv[0] / t),
                                   ("MS X", "X", r["px"], odds["X"], inv[1] / t),
                                   ("MS 2", "2", r["p2"], odds["2"], inv[2] / t)):
            out.append((lab, code, p, o, q))
    key = LINE_KEY.get(odds.get("line"))
    if key and r.get(key) is not None:
        inv = [1 / odds["over"], 1 / odds["under"]]
        t = sum(inv)
        ln = odds["line"]
        out.append((f"{ln} Üst", f"o{ln}", r[key], odds["over"], inv[0] / t))
        out.append((f"{ln} Alt", f"u{ln}", 1 - r[key], odds["under"], inv[1] / t))
    return out


def value_bets(r, odds):
    vb = []
    for lab, code, p, o, q in market_list(r, odds):
        ev = p * o - 1
        if p >= VALUE_MIN_P and VALUE_MIN_EV <= ev <= VALUE_MAX_EV:
            vb.append({"lab": lab, "code": code, "p": p, "o": o, "q": q, "ev": ev})
    return sorted(vb, key=lambda x: -x["ev"])


def settle(code, hg, ag):
    if code == "1":
        return hg > ag
    if code == "X":
        return hg == ag
    if code == "2":
        return hg < ag
    ln = float(code[1:])
    return (hg + ag > ln) if code[0] == "o" else (hg + ag < ln)


def fair(p):
    return "-" if not p or p <= 0 else f"{1 / p:.2f}"


# ------------------------------------------------------------ takım istatistik
def team_history(matches):
    th = defaultdict(list)
    for m in matches:
        ht = m.get("ht")
        th[m["hid"]].append((m["date"], m["hg"], m["ag"],
                             ht[0] if ht else None, ht[1] if ht else None, True))
        th[m["aid"]].append((m["date"], m["ag"], m["hg"],
                             ht[1] if ht else None, ht[0] if ht else None, False))
    return th


def summarize(rows):
    n = len(rows)
    if n == 0:
        return None
    s = {
        "n": n,
        "gf": sum(r[1] for r in rows) / n, "ga": sum(r[2] for r in rows) / n,
        "w": sum(1 for r in rows if r[1] > r[2]),
        "d": sum(1 for r in rows if r[1] == r[2]),
        "l": sum(1 for r in rows if r[1] < r[2]),
        "o25": sum(1 for r in rows if r[1] + r[2] >= 3) / n,
        "btts": sum(1 for r in rows if r[1] > 0 and r[2] > 0) / n,
        "n1": 0, "gf1": None, "ga1": None, "iy05": None,
    }
    hr = [r for r in rows if r[3] is not None]
    if hr:
        s["n1"] = len(hr)
        s["gf1"] = sum(r[3] for r in hr) / len(hr)
        s["ga1"] = sum(r[4] for r in hr) / len(hr)
        s["iy05"] = sum(1 for r in hr if r[3] + r[4] >= 1) / len(hr)
    return s


def season_start(now, calendar):
    if calendar:
        return dt.datetime(now.year, 1, 1, tzinfo=UTC)
    y = now.year if now.month >= 7 else now.year - 1
    return dt.datetime(y, 7, 1, tzinfo=UTC)


# ------------------------------------------------------------ geriye dönük test
MARKETS = [("1.5Ü", "o15"), ("2.5Ü", "o25"), ("3.5Ü", "o35"), ("KG", "btts"),
           ("İY 0.5Ü", "iy05"), ("İY 1.5Ü", "iy15"), ("İY KG", "iykg")]


def actuals(m):
    tg = m["hg"] + m["ag"]
    a = {"o15": tg >= 2, "o25": tg >= 3, "o35": tg >= 4,
         "btts": m["hg"] > 0 and m["ag"] > 0,
         "iy05": None, "iy15": None, "iykg": None}
    if m.get("ht"):
        h1, a1 = m["ht"]
        a.update(iy05=h1 + a1 >= 1, iy15=h1 + a1 >= 2, iykg=h1 > 0 and a1 > 0)
    return a


def backtest_raw(matches, now):
    """Son günlerin her maçı için o günden önceki veriyle kurulmuş modelin ham tahmini."""
    out = []
    if len(matches) < 60:
        return out
    dates = [m["date"] for m in matches]
    t0 = now - dt.timedelta(days=BACKTEST_DAYS + CALIB_DAYS)
    days = sorted({m["date"].date() for m in matches if m["date"] >= t0})
    for d in days:
        ref = dt.datetime(d.year, d.month, d.day, tzinfo=UTC)
        idx = bisect.bisect_left(dates, ref)
        model = build_model(matches[:idx], ref)
        if not model:
            continue
        for m in matches[idx:]:
            if m["date"].date() != d:
                continue
            lam = lambdas(model, m["hid"], m["aid"])
            hl = half_lams(model, m["hid"], m["aid"], *lam)
            out.append({"date": ref, "lam": lam, "mu": mus(model), "rho": model["rho"],
                        "sh": (hl[0] / lam[0], hl[1] / lam[1]) if hl else None,
                        "hg": m["hg"], "ag": m["ag"], "m": m})
    return out


def bt_eval(raw, kc):
    out = []
    for x in raw:
        m = x["m"]
        lam = calibrate(x["lam"], x["mu"], kc)
        hl = (lam[0] * x["sh"][0], lam[1] * x["sh"][1]) if x["sh"] else None
        r = analyze(*lam, rho=x["rho"], half=hl, joint=False)
        vb = [(v["code"], v["o"], settle(v["code"], m["hg"], m["ag"]))
              for v in value_bets(r, m.get("odds"))]
        out.append({
            "vb": vb, "has_odds": bool(m.get("odds")),
            "pred": {k: r.get(k) for _, k in MARKETS},
            "act": actuals(m),
            "p": (r["p1"], r["px"], r["p2"]),
            "res": res3(m["hg"], m["ag"]),
        })
    return out


def market_stats(rows, key):
    sel = [(r["pred"][key], 1.0 if r["act"][key] else 0.0) for r in rows
           if r["pred"].get(key) is not None and r["act"].get(key) is not None]
    n = len(sel)
    if n < 10:
        return None
    acc = sum(1 for p, a in sel if (p >= 0.5) == (a == 1.0)) / n
    brier = sum((p - a) ** 2 for p, a in sel) / n
    base = sum(a for _, a in sel) / n
    bb = sum((base - a) ** 2 for _, a in sel) / n
    skill = 1 - brier / bb if bb > 0 else None
    return {"n": n, "acc": acc, "skill": skill}


def ms_stats(rows):
    n = len(rows)
    if n < 10:
        return None
    acc = sum(1 for r in rows if max(range(3), key=lambda i: r["p"][i]) == r["res"]) / n
    freq = [sum(1 for r in rows if r["res"] == k) / n for k in range(3)]
    brier = sum(sum((r["p"][k] - (r["res"] == k)) ** 2 for k in range(3)) for r in rows) / n
    bb = sum(sum((freq[k] - (r["res"] == k)) ** 2 for k in range(3)) for r in rows) / n
    return {"n": n, "acc": acc, "skill": 1 - brier / bb if bb > 0 else None}


def calibration(pairs):
    edges = [0, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 1.01]
    res = []
    for lo, hi in zip(edges, edges[1:]):
        sel = [(p, a) for p, a in pairs if lo <= p < hi]
        if len(sel) >= 5:
            res.append((lo, hi, len(sel), sum(p for p, _ in sel) / len(sel),
                        sum(1 for _, a in sel if a) / len(sel)))
    return res


# ---------------------------------------------------------------- ana akış
def pct(x):
    return "-" if x is None else f"{x * 100:.0f}%"


def cls(x):
    if x is None:
        return "lo"
    x = round(x, 2)                     # renk, ekranda yazan yuvarlanmış sayıyla aynı olsun
    return "hi" if x >= 0.6 else ("mid" if x >= 0.45 else "lo")


def day_window(now):
    loc = now.astimezone(TR)
    d0 = dt.datetime(loc.year, loc.month, loc.day, DAY_START, tzinfo=TR)
    if loc.hour < DAY_START:
        d0 -= dt.timedelta(days=1)
    return d0, d0 + dt.timedelta(days=1)


def process_league(slug, name, calendar, now):
    info = {"slug": slug, "name": name, "cards": [], "err": "", "nfin": 0,
            "avg90": None, "bt": [], "model": None, "results": {}, "rev": None, "kc": None}
    try:
        finished, allm = fetch_league(slug, now)
    except Exception as e:  # noqa
        info["err"] = f"Veri alınamadı: {e}"
        return info
    info["results"] = {m["id"]: [m["hg"], m["ag"]] + (list(m["ht"]) if m.get("ht") else [None, None])
                       for m in finished}
    d0, d1 = day_window(now)
    past = [m for m in finished if m["date"] < d0]      # bugünün sonuçları modele sızmasın
    info["nfin"] = len(past)
    if len(past) < 30:
        info["err"] = f"Yetersiz geçmiş veri ({len(past)} maç)"
        return info

    c90 = [m for m in past if m["date"] >= now - dt.timedelta(days=90)]
    if c90:
        info["avg90"] = sum(m["hg"] + m["ag"] for m in c90) / len(c90)

    model = build_model(past, d0.astimezone(UTC))
    info["model"] = model
    th = team_history(past)
    ss = season_start(now, calendar)
    todays = [m for m in allm if d0 <= m["date"] < d1]
    info["raw"] = backtest_raw(finished, now)
    info["_ctx"] = (model, past, th, ss, todays)
    return info


def finish_league(info, now, pool_eval, pool_all):
    """Ayarı (kalibrasyonu) uygular, doğruluk testini ve bugünün kartlarını üretir."""
    if info["err"] or "_ctx" not in info:
        return info
    model, past, th, ss, todays = info.pop("_ctx")
    raw = info.pop("raw")
    name = info["name"]
    cut = now - dt.timedelta(days=BACKTEST_DAYS)
    old = [x for x in raw if x["date"] < cut]
    # doğruluk testi: ayar sadece test günlerinden ÖNCEKİ maçlarla yapılır
    kc_eval = fit_kc(old) if len(old) >= MIN_CALIB else pool_eval
    info["bt"] = bt_eval([x for x in raw if x["date"] >= cut], kc_eval)
    own = len(raw) >= MIN_CALIB
    kc = fit_kc(raw) if own else pool_all
    info["kc"] = kc
    info["kc_src"] = "lig" if own else "ortak"
    mu = mus(model)
    past_lams = [(lambdas(model, m["hid"], m["aid"]), m) for m in past]
    hts = [m for m in past if m.get("ht")]
    if len(hts) >= 50:                  # ligde İY/MS tersine dönüş sıklığı
        info["rev"] = (sum(1 for m in hts if m["ht"][0] < m["ht"][1] and m["hg"] > m["ag"]) / len(hts),
                       sum(1 for m in hts if m["ht"][0] > m["ht"][1] and m["hg"] < m["ag"]) / len(hts))

    def tstat(tid, home):
        rows = sorted(th.get(tid, []), key=lambda r: r[0])
        venue = [r for r in rows if r[5] == home]
        return {
            "l10": summarize(rows[-LAST_N:]),
            "venue": summarize(venue[-5:]),
            "season": summarize([r for r in rows if r[0] >= ss]),
        }

    for m in todays:
        lam_raw = lambdas(model, m["hid"], m["aid"])
        lam = calibrate(lam_raw, mu, kc)
        hl = half_lams(model, m["hid"], m["aid"], *lam)
        r = analyze(*lam, rho=model["rho"], half=hl)
        low = [n for t, n in ((m["hid"], m["home"]), (m["aid"], m["away"]))
               if model["games"].get(t, 0) < LOW_DATA]
        nb = neighbors(past_lams, *lam_raw)
        ss_ = sim_stats(nb)
        surprise = []
        if r.get("htft") and ss_["nht"] >= 20:
            for code, pk, rk in (("2/1", "p21", "r21"), ("1/2", "p12", "r12")):
                p, k = r[pk], ss_[rk]
                rate = k / ss_["nht"]
                if p >= SURPRISE_MIN_P and k >= 2:
                    surprise.append({"t": code, "p": p, "k": k, "n": ss_["nht"], "rate": rate,
                                     "score": (p + rate) / 2})
        info["cards"].append({
            "id": m["id"], "league": name, "kick": m["date"],
            "odds": m.get("odds"), "vb": value_bets(r, m.get("odds")),
            "simst": ss_, "surprise": surprise,
            "time": m["date"].astimezone(TR).strftime("%H:%M"),
            "day": m["date"].astimezone(TR).strftime("%d.%m"),
            "home": m["home"], "away": m["away"], "lam": lam, "r": r, "low": low,
            "state": m["state"], "score": (m["hg"], m["ag"]) if m["done"] else None,
            "hs": tstat(m["hid"], True), "as": tstat(m["aid"], False),
            "sim": [sim_text(x) for x in nb[:5]],
        })
    info["cards"].sort(key=lambda c: (c["day"], c["time"]))
    return info


# ------------------------------------------------------------ kayıt ve karne
PRED_KEYS = ["p1", "px", "p2", "o15", "o25", "o35", "btts", "iy05", "iy15", "iykg", "p21", "p12"]


def load_store():
    try:
        with open(STORE, encoding="utf-8") as f:
            st = json.load(f)
        st.setdefault("preds", {})
        st.setdefault("meta", {})
        return st
    except Exception:  # noqa
        return {"preds": {}, "meta": {}}


def save_store(st):
    os.makedirs(os.path.dirname(STORE), exist_ok=True)
    with open(STORE, "w", encoding="utf-8") as f:
        json.dump(st, f, ensure_ascii=False, separators=(",", ":"))


def update_store(st, leagues, now):
    d0, _ = day_window(now)
    preds = st["preds"]
    # 1) bugünün başlamamış maçlarını kaydet (başlamış maç kaydedilmez, hile olmasın)
    for L in leagues:
        for c in L["cards"]:
            if c["state"] != "pre" or c["kick"] <= now:
                continue
            r = c["r"]
            preds[c["id"]] = {
                "d": f"{d0:%Y-%m-%d}", "k": c["kick"].isoformat(), "lg": c["league"],
                "h": c["home"], "a": c["away"],
                "p": {k: round(r[k], 4) for k in PRED_KEYS if r.get(k) is not None},
                "ts": r["top"][0][0],
                "vb": [{"l": v["lab"], "c": v["code"], "o": v["o"], "p": round(v["p"], 4)} for v in c["vb"]],
                "sur": [{"t": x["t"], "p": round(x["p"], 4)} for x in c["surprise"]],
                "res": preds.get(c["id"], {}).get("res"),
            }
    # 2) sonuçlanan maçları işle
    results = {}
    for L in leagues:
        results.update(L["results"])
    for pid, e in preds.items():
        if e.get("res") is None and pid in results:
            e["res"] = results[pid]
    # 3) eskileri sil
    cut = f"{(d0 - dt.timedelta(days=KEEP_DAYS)):%Y-%m-%d}"
    st["preds"] = {k: v for k, v in preds.items() if v["d"] >= cut}


BIN_MARKETS = [("1.5 Üst/Alt", "o15", None), ("2.5 Üst/Alt", "o25", None), ("3.5 Üst/Alt", "o35", None),
               ("KG Var/Yok", "btts", None), ("İY 0.5 Üst/Alt", "iy05", "ht"),
               ("İY 1.5 Üst/Alt", "iy15", "ht"), ("İY KG Var/Yok", "iykg", "ht")]


def outcome(key, res):
    hg, ag, h1, a1 = res
    if key in ("o15", "o25", "o35"):
        return hg + ag > {"o15": 1.5, "o25": 2.5, "o35": 3.5}[key]
    if key == "btts":
        return hg > 0 and ag > 0
    if h1 is None:
        return None
    if key == "iy05":
        return h1 + a1 >= 1
    if key == "iy15":
        return h1 + a1 >= 2
    if key == "iykg":
        return h1 > 0 and a1 > 0
    return None


def grade(entries):
    """Bir grup kayıtlı tahminin karnesi."""
    g = {"n": len(entries), "mk": {}, "ms": [0, 0], "ts": [0, 0],
         "vb": [0, 0, 0.0], "sur": [0, 0]}
    for label, key, _ in BIN_MARKETS:
        hit = tot = 0
        for e in entries:
            p = e["p"].get(key)
            if p is None or CONF > p > 1 - CONF:
                continue
            o = outcome(key, e["res"])
            if o is None:
                continue
            tot += 1
            hit += (p >= CONF) == o
        g["mk"][label] = (hit, tot)
    for e in entries:
        hg, ag, h1, a1 = e["res"]
        p = [e["p"].get("p1", 0), e["p"].get("px", 0), e["p"].get("p2", 0)]
        if max(p) >= 0.55:
            g["ms"][1] += 1
            g["ms"][0] += max(range(3), key=lambda i: p[i]) == res3(hg, ag)
        g["ts"][1] += 1
        g["ts"][0] += e["ts"] == f"{hg}-{ag}"
        for v in e.get("vb", []):
            win = settle(v["c"], hg, ag)
            g["vb"][1] += 1
            g["vb"][0] += win
            g["vb"][2] += (v["o"] - 1) if win else -1
        for x in e.get("sur", []):
            if h1 is None:
                continue
            g["sur"][1] += 1
            if x["t"] == "2/1":
                g["sur"][0] += h1 < a1 and hg > ag
            else:
                g["sur"][0] += h1 > a1 and hg < ag
    return g


def periods(st, now):
    d0, _ = day_window(now)
    done = [e for e in st["preds"].values() if e.get("res")]
    yday = f"{(d0 - dt.timedelta(days=1)):%Y-%m-%d}"
    d7 = f"{(d0 - dt.timedelta(days=7)):%Y-%m-%d}"
    d30 = f"{(d0 - dt.timedelta(days=30)):%Y-%m-%d}"
    return [("Dün", grade([e for e in done if e["d"] == yday])),
            ("7 gün", grade([e for e in done if e["d"] >= d7])),
            ("30 gün", grade([e for e in done if e["d"] >= d30])),
            ("Tümü", grade(done))]


def site_url():
    repo = os.environ.get("GITHUB_REPOSITORY", "")
    if "/" in repo:
        owner, name = repo.split("/", 1)
        return f"https://{owner.lower()}.github.io/{name}/"
    return ""


def send_mail(st, leagues, now):
    user, pw = os.environ.get("MAIL_USER"), os.environ.get("MAIL_PASS")
    to = os.environ.get("MAIL_TO") or user
    if not user or not pw:
        print("E-posta ayarı yok, atlandı.")
        return
    d0, _ = day_window(now)
    today = f"{d0:%Y-%m-%d}"
    if st["meta"].get("last_mail") == today:
        print("Bugün e-posta zaten gönderildi.")
        return
    body = (f"<div style='font-family:system-ui,sans-serif;max-width:560px'>"
            f"<h2 style='margin:0 0 8px'>Günün Maçları · {d0:%d.%m.%Y}</h2>")
    url = site_url()
    if url:
        body += f"<p><a href='{url}'>Sayfayı aç</a></p>"
    body += karne_table(periods(st, now), compact=True)
    body += radar_html(leagues, compact=True)
    body += value_html(leagues, compact=True)
    body += "<p style='color:#888;font-size:12px'>Model tahmindir, kâr garantisi vermez.</p></div>"
    msg = EmailMessage()
    msg["Subject"] = f"Günün maçları ve karne · {d0:%d.%m}"
    msg["From"] = user
    msg["To"] = to
    msg.set_content("Bu e-posta HTML görüntüleme gerektirir.")
    msg.add_alternative(body, subtype="html")
    try:
        with smtplib.SMTP_SSL("smtp.gmail.com", 465, timeout=30) as s:
            s.login(user, pw)
            s.send_message(msg)
        st["meta"]["last_mail"] = today
        print("E-posta gönderildi:", to)
    except Exception as e:  # noqa
        print("E-posta gönderilemedi:", type(e).__name__, str(e)[:120])


def main():
    now = dt.datetime.now(UTC)
    leagues = []
    for slug, name, cal in LEAGUES:
        print("Lig:", slug, flush=True)
        leagues.append(process_league(slug, name, cal, now))
    allraw = [x for L in leagues for x in L.get("raw", [])]
    cut = now - dt.timedelta(days=BACKTEST_DAYS)
    pool_eval = fit_kc([x for x in allraw if x["date"] < cut])
    pool_all = fit_kc(allraw)
    print("ortak ayar:", pool_eval, pool_all, flush=True)
    for L in leagues:
        finish_league(L, now, pool_eval, pool_all)
    st = load_store()
    update_store(st, leagues, now)
    write_html(leagues, now, st)
    send_mail(st, leagues, now)
    save_store(st)


# -------------------------------------------------------------------- HTML
CSS = """
:root{--bg:#f4f5f7;--card:#fff;--tx:#1a1a1a;--mu:#666;--hi:#c8f0d2;--mid:#fdf0c4;--lo:#eee;--ac:#0a7d3b;--bd:#ddd;--neg:#c0392b;--warn:#b26a00}
@media (prefers-color-scheme:dark){:root{--bg:#111;--card:#1c1c1e;--tx:#eee;--mu:#999;--hi:#1f5130;--mid:#5a4a14;--lo:#2a2a2c;--ac:#3ecf72;--bd:#333;--neg:#ff6b5e;--warn:#f0a940}}
*{box-sizing:border-box}
body{margin:0;background:var(--bg);color:var(--tx);font-family:system-ui,sans-serif}
header{padding:12px 12px 0}h1{font-size:20px;margin:0}
.upd{color:var(--mu);font-size:12px;margin:6px 0}
nav{position:sticky;top:0;background:var(--bg);display:flex;gap:6px;overflow-x:auto;padding:8px 12px;z-index:5;white-space:nowrap}
nav button{border:1px solid var(--bd);background:var(--card);color:var(--tx);border-radius:16px;padding:7px 12px;font-size:13px;flex:none}
nav button.on{background:var(--ac);color:#fff;border-color:var(--ac)}
nav small{opacity:.7}
.tab{display:none;padding:4px 12px 24px}.tab.on{display:block}
h2{font-size:17px;margin:4px 0 8px}h3{font-size:15px;margin:16px 0 6px}
.card{background:var(--card);border-radius:12px;padding:14px;margin-bottom:12px}
.meta,.row{color:var(--mu);font-size:13px;margin-top:6px}
.row b{color:var(--tx);font-weight:600}
.sec{font-size:11px;text-transform:uppercase;letter-spacing:.05em;color:var(--mu);margin:12px 0 6px}
.grid{display:grid;grid-template-columns:repeat(3,1fr);gap:6px;margin-top:6px}
.b{text-align:center;border-radius:8px;padding:7px 4px;font-size:12px}
.b b{font-size:17px}.hi{background:var(--hi)}.mid{background:var(--mid)}.lo{background:var(--lo)}
.sc{float:right;font-weight:600;color:var(--tx)}
.warn{color:var(--warn);font-size:12px;margin-top:6px}
.wrap{overflow-x:auto;margin-top:6px}
table{border-collapse:collapse;width:100%;font-size:12.5px}
th,td{padding:6px 5px;text-align:left;border-bottom:1px solid var(--bd);white-space:nowrap}
th{color:var(--mu);font-weight:600}
td.n,th.n{text-align:right}
.pos{color:var(--ac);font-weight:600}.neg{color:var(--neg);font-weight:600}
summary{margin-top:10px;font-size:13px;cursor:pointer}li{font-size:13px;color:var(--mu)}
.fire{color:var(--ac);font-weight:700}
.empty,.err{color:var(--mu);font-size:14px;padding:12px 0}
.note{color:var(--mu);font-size:12.5px;line-height:1.45}
.b small{display:block;font-size:10.5px;color:var(--mu);margin-top:1px}
.b.val{outline:2px solid var(--ac);outline-offset:-2px}
.radar{border:2px solid var(--warn);border-radius:12px;padding:12px;margin:10px 0 14px;background:var(--card)}
.radar h3{margin:0 0 6px;color:var(--warn)}
.valbox{border:2px solid var(--ac);border-radius:12px;padding:12px;margin:10px 0 14px;background:var(--card)}
.valbox h3{margin:0 0 6px;color:var(--ac)}
.tag{display:inline-block;font-size:11px;font-weight:700;padding:2px 6px;border-radius:6px;margin-right:4px}
.tag.s{background:var(--warn);color:#fff}.tag.v{background:var(--ac);color:#fff}
tr.hl td{font-weight:700;color:var(--tx)}
"""

JS = """
function show(id){
  document.querySelectorAll('.tab').forEach(function(e){e.classList.toggle('on',e.id===id)});
  document.querySelectorAll('nav button').forEach(function(e){e.classList.toggle('on',e.dataset.t===id)});
  window.scrollTo(0,0);
}
document.querySelectorAll('nav button').forEach(function(b){
  b.addEventListener('click',function(){show(b.dataset.t)});
});
"""

E = html.escape


def box(label, p, odd=None, val=False):
    extra = f"<small>adil {fair(p)}{f' · oran {odd:.2f}' if odd else ''}</small>"
    return f"<div class='b {cls(p)}{' val' if val else ''}'>{label}<br><b>{pct(p)}</b>{extra}</div>"


def num(x, f="{:.1f}"):
    return "-" if x is None else f.format(x)


def stat_row(label, s, ht=True):
    if not s:
        cols = 8 if ht else 6
        return f"<tr><td>{E(label)}</td><td colspan='{cols}'>veri yok</td></tr>"
    out = (f"<tr><td>{E(label)}</td><td class='n'>{s['n']}</td>"
           f"<td class='n'>{num(s['gf'])}</td><td class='n'>{num(s['ga'])}</td>")
    if ht:
        out += f"<td class='n'>{num(s['gf1'])}</td><td class='n'>{num(s['ga1'])}</td>"
    out += (f"<td>{s['w']}G {s['d']}B {s['l']}M</td><td class='n'>{pct(s['o25'])}</td>"
            f"<td class='n'>{pct(s['btts'])}</td></tr>")
    return out


STAT_HEAD = ("<tr><th></th><th class='n'>Maç</th><th class='n'>At</th><th class='n'>Ye</th>"
             "<th class='n'>İY At</th><th class='n'>İY Ye</th><th>G-B-M</th>"
             "<th class='n'>2.5Ü</th><th class='n'>KG</th></tr>")


def card_html(c):
    r = c["r"]
    badge = ""
    if c["score"]:
        badge = f"<span class='sc'>Bitti {c['score'][0]}-{c['score'][1]}</span>"
    elif c["state"] == "in":
        badge = "<span class='sc'>Canlı</span>"
    warn = (f"<div class='warn'>Az veri: {E(', '.join(c['low']))} — tahmin daha belirsiz</div>"
            if c["low"] else "")
    lam, lam1 = c["lam"], r["lam1"]
    exp = f"{lam[0]:.2f} - {lam[1]:.2f} (toplam {lam[0] + lam[1]:.2f})"
    if lam1:
        exp += f" · İY {lam1[0]:.2f} - {lam1[1]:.2f}"
    tg = r["tg"]
    od = c.get("odds") or {}
    vcodes = {v["code"] for v in c["vb"]}
    ln = od.get("line")
    o25 = od.get("over") if ln == 2.5 else None
    o15 = od.get("over") if ln == 1.5 else None
    o35 = od.get("over") if ln == 3.5 else None
    tags = "".join(f"<span class='tag s'>Sürpriz {x['t']}</span>" for x in c["surprise"])
    tags += "".join(f"<span class='tag v'>Değer: {E(v['lab'])}</span>" for v in c["vb"])
    if tags:
        warn = f"<div style='margin-top:6px'>{tags}</div>" + warn

    out = f"""
<div class="card">
  <div class="meta">{c['day']} {c['time']} {badge}</div>
  <h2>{E(c['home'])} - {E(c['away'])}</h2>{warn}
  <div class="sec">Maç sonu</div>
  <div class="grid">{box('MS 1', r['p1'], od.get('1'), '1' in vcodes)}{box('MS X', r['px'], od.get('X'), 'X' in vcodes)}{box('MS 2', r['p2'], od.get('2'), '2' in vcodes)}</div>
  <div class="grid">{box('1.5 Üst', r['o15'], o15, 'o1.5' in vcodes)}{box('2.5 Üst', r['o25'], o25, 'o2.5' in vcodes)}{box('3.5 Üst', r['o35'], o35, 'o3.5' in vcodes)}</div>
  <div class="grid">{box('KG Var', r['btts'])}{box('Ev 0.5Ü', r['h05'])}{box('Dep 0.5Ü', r['a05'])}</div>"""
    if lam1:
        out += f"""
  <div class="sec">İlk yarı</div>
  <div class="grid">{box('İY 0.5Ü', r['iy05'])}{box('İY 1.5Ü', r['iy15'])}{box('İY KG', r['iykg'])}</div>
  <div class="grid">{box('İY 1', r['iy1'])}{box('İY X', r['iyx'])}{box('İY 2', r['iy2'])}</div>"""
    out += f"""
  <div class="row">Beklenen gol: <b>{exp}</b></div>
  <div class="row">Çifte şans: 1X <b>{pct(r['p1'] + r['px'])}</b> · X2 <b>{pct(r['px'] + r['p2'])}</b> · 12 <b>{pct(r['p1'] + r['p2'])}</b></div>
  <div class="row">Toplam gol: 0-1 <b>{pct(tg[0])}</b> · 2-3 <b>{pct(tg[1])}</b> · 4-5 <b>{pct(tg[2])}</b> · 6+ <b>{pct(tg[3])}</b></div>
  <div class="row">Takım golü: Ev 1.5Ü <b>{pct(r['h15'])}</b> · Dep 1.5Ü <b>{pct(r['a15'])}</b></div>"""
    if lam1:
        mo = r.get("more", [None] * 3)
        out += f"""
  <div class="row">2. yarı: 0.5Ü <b>{pct(r['y2_05'])}</b> · 1.5Ü <b>{pct(r['y2_15'])}</b></div>
  <div class="row">Daha golcü yarı: 1. yarı <b>{pct(mo[0])}</b> · 2. yarı <b>{pct(mo[1])}</b> · eşit <b>{pct(mo[2])}</b></div>"""
    out += f"""
  <div class="row">Olası skorlar: <b>{', '.join(f'{s} ({pct(p)})' for s, p in r['top'])}</b></div>"""
    if c["vb"]:
        out += ("<div class='sec'>Değerli oranlar</div><div class='wrap'><table><tr><th>Bahis</th>"
                "<th class='n'>Model</th><th class='n'>Piyasa</th><th class='n'>Oran</th>"
                "<th class='n'>Beklenen getiri</th></tr>")
        for v in c["vb"]:
            out += (f"<tr><td>{E(v['lab'])}</td><td class='n'>{pct(v['p'])}</td><td class='n'>{pct(v['q'])}</td>"
                    f"<td class='n'>{v['o']:.2f}</td><td class='n pos'>+{v['ev'] * 100:.0f}%</td></tr>")
        out += f"</table></div><p class='note'>Oran kaynağı: {E(od.get('src') or 'ESPN')}. Kendi iddaa oranını 'adil oran' ile kıyasla: adil orandan yüksekse değerlidir.</p>"

    # skor tablosu: modelin en olası skorları + benzer maçlarda sık çıkanlar
    sst = c["simst"]
    model_top = sorted(r["scores"].items(), key=lambda x: -x[1])[:6]
    shown = [s_ for s_, _ in model_top]
    for s_, k in sorted(sst["scores"].items(), key=lambda x: -x[1]):
        if k >= 2 and s_ not in shown and len(shown) < 9:
            shown.append(s_)
    out += (f"<div class='sec'>Skor olasılıkları</div><div class='wrap'><table><tr><th>Skor</th>"
            f"<th class='n'>Model</th><th class='n'>Adil oran</th><th class='n'>Benzer {sst['n']} maçta</th></tr>")
    for s_ in shown:
        p = r["scores"].get(s_, 0)
        k = sst["scores"].get(s_, 0)
        out += (f"<tr{' class=hl' if s_ == shown[0] else ''}><td>{s_}</td><td class='n'>{pct(p)}</td>"
                f"<td class='n'>{fair(p)}</td><td class='n'>{k} kez ({pct(k / sst['n']) if sst['n'] else '-'})</td></tr>")
    out += "</table></div>"
    if r.get("p21") is not None:
        out += (f"<div class='row'>İY/MS sürpriz: 2/1 <b>{pct(r['p21'])}</b> (adil {fair(r['p21'])}, benzer maçlarda "
                f"{sst['r21']}/{sst['nht']}) · 1/2 <b>{pct(r['p12'])}</b> (adil {fair(r['p12'])}, benzer maçlarda "
                f"{sst['r12']}/{sst['nht']})</div>")

    if r.get("htft"):
        lab = ["1", "X", "2"]
        rows = "".join(
            f"<tr><td>İY {lab[h]}</td>" +
            "".join(f"<td class='n'>{pct(r['htft'].get((h, k), 0))}</td>" for k in range(3)) +
            "</tr>" for h in range(3))
        out += (f"<details><summary>İY/MS olasılıkları</summary><div class='wrap'><table>"
                f"<tr><th></th><th class='n'>MS 1</th><th class='n'>MS X</th><th class='n'>MS 2</th></tr>"
                f"{rows}</table></div></details>")

    hs, as_ = c["hs"], c["as"]
    out += (f"<div class='sec'>Son {LAST_N} maç (ortalama)</div><div class='wrap'><table>{STAT_HEAD}"
            f"{stat_row(c['home'], hs['l10'])}{stat_row(c['away'], as_['l10'])}</table></div>")
    out += (f"<details><summary>Evde / deplasmanda ve sezon</summary><div class='wrap'><table>{STAT_HEAD}"
            f"{stat_row(c['home'] + ' (evde son 5)', hs['venue'])}"
            f"{stat_row(c['away'] + ' (dışarıda son 5)', as_['venue'])}"
            f"{stat_row(c['home'] + ' (sezon)', hs['season'])}"
            f"{stat_row(c['away'] + ' (sezon)', as_['season'])}</table></div></details>")
    sim = "".join(f"<li>{E(s)}</li>" for s in c["sim"])
    out += f"<details><summary>Benzer geçmiş maçlar</summary><ul>{sim}</ul></details></div>"
    return out


def radar_html(leagues, compact=False):
    items = [(x, c) for L in leagues for c in L["cards"] if not c["score"] for x in c["surprise"]]
    items.sort(key=lambda t: -t[0]["score"])
    if compact and not items:
        return ""
    out = ("<div class='radar' style='border:2px solid #b26a00;border-radius:12px;padding:12px;margin:10px 0'>"
           "<h3 style='margin:0 0 6px;color:#b26a00'>Sürpriz radarı: İY/MS 2/1 ve 1/2</h3>")
    if not items:
        return out + ("<p class='note'>Bugün modelin ve benzer maçların birlikte işaret ettiği bir "
                      "tersine dönüş adayı yok.</p></div>")
    out += ("<p class='note'>Devre sonucu tersine dönebilecek maçlar. Model olasılığı en az "
            f"%{SURPRISE_MIN_P * 100:.1f} ve benzer geçmiş maçlarda en az 2 kez yaşanmış olanlar.</p>"
            "<div class='wrap'><table><tr><th>Maç</th><th>İY/MS</th><th class='n'>Model</th>"
            "<th class='n'>Adil</th><th class='n'>Benzer</th></tr>")
    for x, c in items[:6]:
        out += (f"<tr><td>{c['time']} {E(c['home'])} - {E(c['away'])}<br><span class='note'>{E(c['league'])}</span></td>"
                f"<td><b>{x['t']}</b></td><td class='n'>{pct(x['p'])}</td><td class='n'>{fair(x['p'])}</td>"
                f"<td class='n'>{x['k']}/{x['n']}</td></tr>")
    return out + "</table></div></div>"


def value_html(leagues, compact=False):
    items = [(v, c) for L in leagues for c in L["cards"] if not c["score"] for v in c["vb"]]
    items.sort(key=lambda t: -t[0]["ev"])
    if compact and not items:
        return ""
    out = ("<div class='valbox' style='border:2px solid #0a7d3b;border-radius:12px;padding:12px;margin:10px 0'>"
           "<h3 style='margin:0 0 6px;color:#0a7d3b'>Değerli oranlar</h3>")
    if not items:
        return out + "<p class='note'>Bugün oranı bilinen maçlarda değerli bulunan bahis yok.</p></div>"
    out += ("<p class='note'>Modelin olasılığı, oranın ima ettiğinden yüksek olan bahisler. Beklenen "
            "getiri = model olasılığı × oran − 1.</p><div class='wrap'><table><tr><th>Maç</th><th>Bahis</th>"
            "<th class='n'>Model</th><th class='n'>Oran</th><th class='n'>Getiri</th></tr>")
    for v, c in items[:8]:
        out += (f"<tr><td>{c['time']} {E(c['home'])} - {E(c['away'])}</td><td>{E(v['lab'])}</td>"
                f"<td class='n'>{pct(v['p'])}</td><td class='n'>{v['o']:.2f}</td>"
                f"<td class='n pos'>+{v['ev'] * 100:.0f}%</td></tr>")
    return out + "</table></div></div>"


def summary_tab(leagues):
    act = []
    for L in leagues:
        cs = L["cards"]
        if cs:
            avg = lambda k: (sum(c["r"].get(k) or 0 for c in cs) / len(cs))  # noqa
            exp = sum(c["lam"][0] + c["lam"][1] for c in cs) / len(cs)
            act.append((exp, L, avg("o25"), avg("btts"),
                        avg("iy05") if all(c["r"].get("iy05") is not None for c in cs) else None))
    act.sort(key=lambda x: (len(x[1]["cards"]) >= 2, x[0]), reverse=True)
    out = "<h2>Günün özeti</h2>" + radar_html(leagues) + value_html(leagues)
    if act:
        top = act[0]
        out += (f"<p><span class='fire'>Günün en golcü ligi: {E(top[1]['name'])}</span> "
                f"({len(top[1]['cards'])} maç, maç başı beklenen {top[0]:.2f} gol)</p>")
    else:
        out += "<p class='empty'>Bugün takip edilen liglerde analiz edilebilen maç yok.</p>"
    out += ("<div class='wrap'><table><tr><th>Lig</th><th class='n'>Maç</th><th class='n'>Bekl. gol</th>"
            "<th class='n'>2.5Ü</th><th class='n'>KG</th><th class='n'>İY 0.5Ü</th>"
            "<th class='n'>Son 90g</th></tr>")
    for exp, L, o25, btts, iy05 in act:
        out += (f"<tr><td>{E(L['name'])}</td><td class='n'>{len(L['cards'])}</td>"
                f"<td class='n'>{exp:.2f}</td><td class='n'>{pct(o25)}</td><td class='n'>{pct(btts)}</td>"
                f"<td class='n'>{pct(iy05)}</td><td class='n'>{num(L['avg90'], '{:.2f}')}</td></tr>")
    out += "</table></div><p class='note'>Son 90g: ligde son 90 günde maç başı gerçekleşen gol.</p>"

    allc = [(c, L["name"]) for L in leagues for c in L["cards"] if not c["score"]]
    for title, key in (("2.5 Üst", "o25"), ("KG Var", "btts"), ("İY 0.5 Üst", "iy05"),
                       ("İY 1.5 Üst", "iy15")):
        sel = sorted([x for x in allc if x[0]["r"].get(key) is not None],
                     key=lambda x: -x[0]["r"][key])[:6]
        if not sel:
            continue
        out += (f"<h3>En yüksek {title}</h3><div class='wrap'><table>"
                f"<tr><th>Maç</th><th>Lig</th><th class='n'>%</th></tr>")
        for c, ln in sel:
            out += (f"<tr><td>{c['time']} {E(c['home'])} - {E(c['away'])}</td><td>{E(ln)}</td>"
                    f"<td class='n'>{pct(c['r'][key])}</td></tr>")
        out += "</table></div>"

    errs = [f"{L['name']}: {L['err']}" for L in leagues if L["err"]]
    if errs:
        out += "<h3>Sorunlu ligler</h3>" + "".join(f"<p class='err'>{E(x)}</p>" for x in errs)
    return out


def karne_table(per, compact=False):
    head = "".join(f"<th class='n'>{lab}</th>" for lab, _ in per)
    st = "style='border-collapse:collapse;font-size:13px'" if compact else ""
    out = f"<div class='wrap'><table {st}><tr><th>Ölçü</th>{head}</tr>"

    sm = "style='color:#888;font-size:11px'"

    def ratio(h, t):
        return f"<b>{h / t * 100:.0f}%</b><br><span {sm}>{h}/{t}</span>" if t else "-"
    out += "<tr><td>Sonuçlanan maç</td>" + "".join(f"<td class='n'>{g['n']}</td>" for _, g in per) + "</tr>"
    out += "<tr><td>MS (≥%55)</td>" + "".join(f"<td class='n'>{ratio(*g['ms'])}</td>" for _, g in per) + "</tr>"
    for label, _, _ in BIN_MARKETS:
        out += (f"<tr><td>{label}</td>" +
                "".join(f"<td class='n'>{ratio(*g['mk'][label])}</td>" for _, g in per) + "</tr>")
    out += "<tr><td>En olası skor</td>" + "".join(f"<td class='n'>{ratio(*g['ts'])}</td>" for _, g in per) + "</tr>"
    out += "<tr><td>Sürpriz radarı</td>" + "".join(f"<td class='n'>{ratio(*g['sur'])}</td>" for _, g in per) + "</tr>"
    out += "<tr><td>Değer isabet</td>" + "".join(
        f"<td class='n'>{ratio(g['vb'][0], g['vb'][1])}</td>" for _, g in per) + "</tr>"
    cells = ""
    for _, g in per:
        w, t, pr = g["vb"]
        if not t:
            cells += "<td class='n'>-</td>"
        else:
            col = "#0a7d3b" if pr > 0 else "#c0392b"
            cells += (f"<td class='n' style='color:{col};font-weight:600'>{pr:+.1f}<br>"
                      f"<span {sm}>ROI {pr / t * 100:+.0f}%</span></td>")
    out += f"<tr><td>Değer kâr (birim)</td>{cells}</tr></table></div>"
    return out


def karne_tab(st, now):
    per = periods(st, now)
    out = ("<h2>Karne</h2><p class='note'>Bot her sabah başlamamış maçların tahminini kaydeder, maç "
           "bitince sonucu işler. Burada sadece maç başlamadan yapılmış tahminler sayılır. Üst/Alt ve "
           f"KG satırlarında model %{CONF * 100:.0f} ve üstü (ya da %{(1 - CONF) * 100:.0f} ve altı) "
           "dediği maçlar sayılır. Değerli oran kârı, her bahse 1 birim yatırılmış gibi hesaplanır.</p>")
    out += karne_table(per)
    d0, _ = day_window(now)
    yday = f"{(d0 - dt.timedelta(days=1)):%Y-%m-%d}"
    yv = [(e, v) for e in st["preds"].values() if e["d"] == yday and e.get("res") for v in e.get("vb", [])]
    if yv:
        out += ("<h3>Dünün değerli oranları</h3><div class='wrap'><table><tr><th>Maç</th><th>Bahis</th>"
                "<th class='n'>Oran</th><th class='n'>Skor</th><th class='n'>Sonuç</th></tr>")
        for e, v in yv:
            hg, ag = e["res"][0], e["res"][1]
            win = settle(v["c"], hg, ag)
            out += (f"<tr><td>{E(e['h'])} - {E(e['a'])}</td><td>{E(v['l'])}</td><td class='n'>{v['o']:.2f}</td>"
                    f"<td class='n'>{hg}-{ag}</td><td class='n {'pos' if win else 'neg'}'>"
                    f"{'Tuttu' if win else 'Yattı'}</td></tr>")
        out += "</table></div>"
    days = sorted({e["d"] for e in st["preds"].values() if e.get("res")}, reverse=True)[:14]
    if days:
        out += ("<h3>Son 14 gün</h3><div class='wrap'><table><tr><th>Gün</th><th class='n'>Maç</th>"
                "<th class='n'>2.5 Ü/A</th><th class='n'>KG</th><th class='n'>Değer kâr</th></tr>")
        for d in days:
            g = grade([e for e in st["preds"].values() if e["d"] == d and e.get("res")])
            h25, t25 = g["mk"]["2.5 Üst/Alt"]
            hk, tk = g["mk"]["KG Var/Yok"]
            c25 = f"{h25}/{t25}" if t25 else "-"
            ckg = f"{hk}/{tk}" if tk else "-"
            cvb = f"{g['vb'][2]:+.1f}" if g["vb"][1] else "-"
            out += (f"<tr><td>{d[8:]}.{d[5:7]}</td><td class='n'>{g['n']}</td>"
                    f"<td class='n'>{c25}</td><td class='n'>{ckg}</td><td class='n'>{cvb}</td></tr>")
        out += "</table></div>"
    pend = sum(1 for e in st["preds"].values() if not e.get("res"))
    out += (f"<p class='note'>Kayıtlı tahmin: {len(st['preds'])} · sonucu beklenen: {pend}. Kayıtlar "
            f"GitHub'daki <b>{STORE}</b> dosyasında, son {KEEP_DAYS} gün tutulur.</p>")
    return out


def skill_td(s):
    if not s or s["skill"] is None:
        return "<td class='n'>-</td>"
    v = s["skill"] * 100
    return f"<td class='n {'pos' if v > 0 else 'neg'}'>{v:+.0f}</td>"


def accuracy_tab(leagues):
    allrows = [r for L in leagues for r in L["bt"]]
    groups = [L for L in leagues if L["bt"]] + [{"name": "TÜMÜ", "bt": allrows}]
    heads = "".join(f"<th class='n'>{lab}</th>" for lab, _ in MARKETS)
    out = (f"<h2>Model doğruluğu</h2><p class='note'>Son {BACKTEST_DAYS} günün her maçı, yalnızca "
           "o günden önceki verilerle tahmin edildi ve gerçek sonuçla kıyaslandı. Yüzde ayarı da "
           f"sadece bundan önceki {CALIB_DAYS} günle yapıldı, yani test sınavı görmeden yapılıyor.</p>")

    out += ("<h3>İsabet</h3><p class='note'>Model %50 üstü dediğinde 'olur', altı dediğinde "
            "'olmaz' sayıldı. 1.5Ü gibi zaten sık olan bahislerde yüksek isabet tek başına "
            "bir şey kanıtlamaz, aşağıdaki tabloya bakın.</p>")
    out += f"<div class='wrap'><table><tr><th>Lig</th><th class='n'>Maç</th><th class='n'>MS</th>{heads}</tr>"
    for L in groups:
        ms = ms_stats(L["bt"])
        if not ms:
            continue
        out += f"<tr><td>{E(L['name'])}</td><td class='n'>{ms['n']}</td><td class='n'>{pct(ms['acc'])}</td>"
        for _, k in MARKETS:
            s = market_stats(L["bt"], k)
            out += f"<td class='n'>{pct(s['acc']) if s else '-'}</td>"
        out += "</tr>"
    out += "</table></div>"

    out += ("<h3>Lig ortalamasından ne kadar iyi?</h3><p class='note'>Brier skoruna göre: "
            "<span class='pos'>pozitif</span> sayı, modelin her maça sadece o ligin ortalamasını "
            "söylemekten daha iyi tahmin ettiği anlamına gelir. 0 civarı = model ek bilgi "
            "getirmiyor, <span class='neg'>negatif</span> = ortalamadan kötü.</p>")
    out += f"<div class='wrap'><table><tr><th>Lig</th><th class='n'>MS</th>{heads}</tr>"
    for L in groups:
        ms = ms_stats(L["bt"])
        if not ms:
            continue
        out += f"<tr><td>{E(L['name'])}</td>{skill_td(ms)}"
        for _, k in MARKETS:
            out += skill_td(market_stats(L["bt"], k))
        out += "</tr>"
    out += "</table></div>"

    cals = [("2.5 Üst", "o25", None), ("KG Var", "btts", None), ("İY 0.5 Üst", "iy05", None),
            ("Beraberlik (MS X)", None, "draw")]
    for title, k, special in cals:
        if special == "draw":
            pairs = [(r["p"][1], r["res"] == 1) for r in allrows]
        else:
            pairs = [(r["pred"][k], r["act"][k]) for r in allrows
                     if r["pred"].get(k) is not None and r["act"].get(k) is not None]
        cal = calibration(pairs)
        if not cal:
            continue
        out += (f"<h3>Kalibrasyon: {title}</h3><p class='note'>Model %X dediğinde gerçekte kaç "
                "kez oldu? İki sütun birbirine ne kadar yakınsa yüzdeler o kadar güvenilir.</p>")
        out += ("<div class='wrap'><table><tr><th>Tahmin aralığı</th><th class='n'>Maç</th>"
                "<th class='n'>Ort. tahmin</th><th class='n'>Gerçekleşen</th></tr>")
        for lo, hi, n, mp, ar in cal:
            out += (f"<tr><td>{lo * 100:.0f}-{min(hi, 1) * 100:.0f}%</td><td class='n'>{n}</td>"
                    f"<td class='n'>{pct(mp)}</td><td class='n'>{pct(ar)}</td></tr>")
        out += "</table></div>"

    out += ("<h3>Değerli oran geçmiş testi</h3><p class='note'>Son günlerde model 'değerli' dediği "
            "her bahse 1 birim yatırsaydı (o maçın kapanış oranıyla) ne olurdu? Kapanış oranı piyasanın en "
            "bilgili hali olduğu için bu zor bir sınavdır.</p>")
    out += ("<div class='wrap'><table><tr><th>Lig</th><th class='n'>Oranlı maç</th><th class='n'>Bahis</th>"
            "<th class='n'>İsabet</th><th class='n'>Kâr</th><th class='n'>ROI</th></tr>")
    any_odds = False
    for L in groups:
        rows = L["bt"]
        no = sum(1 for r in rows if r.get("has_odds"))
        bets = [b for r in rows for b in r.get("vb", [])]
        if not no:
            continue
        any_odds = True
        prof = sum((o - 1) if w else -1 for _, o, w in bets)
        wins = sum(1 for _, _, w in bets if w)
        roi = f"<td class='n {'pos' if prof > 0 else 'neg'}'>{prof / len(bets) * 100:+.0f}%</td>" if bets else "<td class='n'>-</td>"
        out += (f"<tr><td>{E(L['name'])}</td><td class='n'>{no}</td><td class='n'>{len(bets)}</td>"
                f"<td class='n'>{pct(wins / len(bets)) if bets else '-'}</td>"
                f"<td class='n'>{prof:+.1f}</td>{roi}</tr>")
    out += "</table></div>"
    if not any_odds:
        out += "<p class='note'>Geçmiş maçlarda oran verisi bulunamadı; değer testi karne biriktikçe yapılacak.</p>"

    out += ("<h3>Model parametreleri</h3><p class='note'>Ev avantajı: ev sahibinin beklenen "
            "golünün deplasmana oranı. İY payı: gollerin ilk yarıda gelen kısmı. DC ρ: düşük "
            "skorların (0-0, 1-1) düzeltme katsayısı; negatif = beraberlikler sık. İY veri: ilk "
            "yarı skoru bulunabilen maç oranı. Ayar k: 1'den küçükse model fazla uç tahmin ediyordu ve "
            "yüzdeler ortalamaya çekildi. Ayar c: 1'den büyükse model golü az tahmin ediyordu ve artırıldı.</p>")
    out += ("<div class='wrap'><table><tr><th>Lig</th><th class='n'>Ev avantajı</th>"
            "<th class='n'>İY payı</th><th class='n'>DC ρ</th><th class='n'>İY veri</th>"
            "<th class='n'>Ayar k</th><th class='n'>Ayar c</th></tr>")
    for L in leagues:
        m = L.get("model")
        if not m:
            continue
        hm = m.get("half")
        out += (f"<tr><td>{E(L['name'])}</td><td class='n'>{m['ha'] ** 2:.2f}</td>"
                f"<td class='n'>{pct(hm['f']) if hm else '-'}</td><td class='n'>{m['rho']:+.2f}</td>"
                f"<td class='n'>{pct(hm['cov']) if hm else '-'}</td>"
                f"<td class='n'>{L['kc'][0]:.2f}{'*' if L.get('kc_src') == 'ortak' else ''}</td>"
                f"<td class='n'>{L['kc'][1]:.2f}</td></tr>")
    out += ("</table></div><p class='note'>* Bu ligin yeterli geçmiş testi olmadığı için tüm liglerin "
            "ortak ayarı kullanıldı.</p>")
    return out


def write_html(leagues, now, st=None):
    local = now.astimezone(TR)
    order = sorted(range(len(leagues)),
                   key=lambda i: (bool(leagues[i]["err"]), -len(leagues[i]["cards"]), i))
    nav = ["<button data-t='ozet' class='on'>Özet</button>"]
    tabs = [f"<section class='tab on' id='ozet'>{summary_tab(leagues)}</section>"]
    for i in order:
        L = leagues[i]
        tid = f"l{i}"
        nav.append(f"<button data-t='{tid}'>{E(L['name'])} <small>{len(L['cards'])}</small></button>")
        if L["err"]:
            body = f"<p class='err'>{E(L['err'])}</p>"
        elif not L["cards"]:
            body = "<p class='empty'>Bugün bu ligde maç yok.</p>"
        else:
            body = "".join(card_html(c) for c in L["cards"])
        meta = f"{L['nfin']} geçmiş maç verisi"
        if L["avg90"]:
            meta += f" · son 90 gün maç başı {L['avg90']:.2f} gol"
        hm = (L.get("model") or {}).get("half")
        if hm:
            meta += f" · İY verisi maçların {pct(hm['cov'])}'ında var"
        tabs.append(f"<section class='tab' id='{tid}'><h2>{E(L['name'])}</h2>"
                    f"<p class='row'>{meta}</p>{body}</section>")
    nav.append("<button data-t='karne'>Karne</button>")
    tabs.append(f"<section class='tab' id='karne'>{karne_tab(st or {'preds': {}, 'meta': {}}, now)}</section>")
    nav.append("<button data-t='dogruluk'>Doğruluk</button>")
    tabs.append(f"<section class='tab' id='dogruluk'>{accuracy_tab(leagues)}</section>")

    d0, d1 = day_window(now)
    page = (f"<!doctype html><html lang='tr'><head><meta charset='utf-8'>"
            f"<meta name='viewport' content='width=device-width, initial-scale=1'>"
            f"<title>Günün Maçları</title><style>{CSS}</style></head><body>"
            f"<header><h1>Günün Maçları</h1><div class='upd'>Güncelleme: {local:%d.%m.%Y %H:%M} · "
            f"Maçlar: {d0:%d.%m %H:%M} - {d1:%d.%m %H:%M} · Model tahmindir, kâr garantisi vermez."
            f"</div></header><nav>{''.join(nav)}</nav>{''.join(tabs)}<script>{JS}</script></body></html>")
    with open("index.html", "w", encoding="utf-8") as f:
        f.write(page)


if __name__ == "__main__":
    main()
