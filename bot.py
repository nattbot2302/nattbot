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
    ("ned.1", "Hollanda Eredivisie", False),
    ("ned.2", "Hollanda 2. Lig", False),
    ("eng.2", "İngiltere Championship", False),
    ("eng.3", "İngiltere 1. Lig (League One)", False),
    ("eng.4", "İngiltere 2. Lig (League Two)", False),
    ("aut.1", "Avusturya Bundesliga", False),
    ("bel.1", "Belçika Pro Lig", False),
    ("uefa.champions", "Şampiyonlar Ligi", False),
    ("uefa.europa", "Avrupa Ligi", False),
    ("uefa.europa.conf", "Konferans Ligi", False),
    ("rus.1", "Rusya Premier Lig", False),
    ("gre.1", "Yunanistan Süper Lig", False),
    ("ksa.1", "Suudi Arabistan Pro Lig", False),
    ("jpn.1", "Japonya J1 Lig", False),
    ("chn.1", "Çin Süper Lig", True),
    ("aus.1", "Avustralya A-Lig", False),
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


def goal_minute(d):
    """Gol dakikası (1-90; uzatma dakikaları 45 / 90 sayılır)."""
    clk = d.get("clock") or {}
    mt = re.match(r"\s*(\d+)", str(clk.get("displayValue") or ""))
    if mt:
        return max(1, min(120, int(mt.group(1))))
    v = clk.get("value")
    if v is None:
        return None
    return max(1, min(120, int(math.ceil(float(v) / 60))))


def goal_list(comp, hid, aid, hg, ag):
    """Gollerin dakikaları: ev sahibi golü +dakika, deplasman golü -dakika. Emin olamazsa None."""
    if hg is None or ag is None:
        return None
    if hg + ag == 0:
        return []
    det = comp.get("details")
    if not det:
        return None
    goals = [d for d in det if d.get("scoringPlay") and not d.get("shootout")]
    for flip in (False, True):
        out, ok = [], True
        for d in goals:
            tid = str((d.get("team") or {}).get("id", ""))
            if flip and d.get("ownGoal"):
                tid = aid if tid == hid else (hid if tid == aid else tid)
            mn = goal_minute(d)
            if tid not in (hid, aid) or mn is None:
                ok = False
                break
            out.append(mn if tid == hid else -mn)
        if ok and sum(1 for x in out if x > 0) == hg and sum(1 for x in out if x < 0) == ag:
            return sorted(out, key=abs)
    return None


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

    def stat(c, k):
        for x in c.get("statistics") or []:
            if x.get("name") == k:
                try:
                    return float(x.get("displayValue"))
                except (TypeError, ValueError):
                    return None
        return None
    sts = None
    if done:
        hs, hsot, as_, asot = (stat(home, "totalShots"), stat(home, "shotsOnTarget"),
                               stat(away, "totalShots"), stat(away, "shotsOnTarget"))
        if None not in (hs, hsot, as_, asot) and hs + as_ > 0 and hs >= hsot and as_ >= asot:
            sts = {"hs": hs, "hsot": hsot, "as": as_, "asot": asot,
                   "hc": stat(home, "wonCorners"), "ac": stat(away, "wonCorners"), "hp": stat(home, "possessionPct")}
    return {"st": sts,
        "id": ev["id"], "date": date, "hid": hid, "aid": aid,
        "home": name(home), "away": name(away), "hg": hg, "ag": ag,
        "ht": ht_score(comp, hid, aid, hg, ag) if done else None,
        "gm": goal_list(comp, hid, aid, hg, ag) if done else None,
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


W_GRID = (0.0, 0.35, 0.6, 0.8)   # takım gücünde şut verisinin ağırlığı (0 = sadece gol)


def xg_coef(matches):
    """Gol ≈ a·isabetli şut + b·isabetsiz şut (ligin kendi verisinden en küçük kareler)."""
    sxx = sxy = syy = sgx = sgy = 0.0
    n = 0
    for m in matches:
        s = m.get("st")
        if not s:
            continue
        for g, sot, sh in ((m["hg"], s["hsot"], s["hs"]), (m["ag"], s["asot"], s["as"])):
            off = sh - sot
            sxx += sot * sot
            sxy += sot * off
            syy += off * off
            sgx += g * sot
            sgy += g * off
            n += 1
    det = sxx * syy - sxy * sxy
    if n < 100 or det <= 0:
        return None
    a = (sgx * syy - sgy * sxy) / det
    b = (sxx * sgy - sxy * sgx) / det
    if a <= 0:
        return None
    return (a, max(b, 0.0), n)


def xg_of(m, coef):
    s = m.get("st")
    if not s or not coef:
        return None, None
    a, b, _ = coef
    return a * s["hsot"] + b * (s["hs"] - s["hsot"]), a * s["asot"] + b * (s["as"] - s["asot"])


def set_values(matches, coef, w):
    """Takım gücü hesabında kullanılacak 'gol değeri': gol ile şut kalitesinin karışımı."""
    for m in matches:
        xh, xa = xg_of(m, coef)
        if xh is None or w <= 0:
            m["vh"], m["va"] = m["hg"], m["ag"]
        else:
            m["vh"] = (1 - w) * m["hg"] + w * xh
            m["va"] = (1 - w) * m["ag"] + w * xa


def choose_w(finished, now, coef):
    """Şut verisine verilecek ağırlığı geçmiş tahmin başarısına göre seçer."""
    res = {}
    cov = sum(1 for m in finished if m.get("st")) / max(len(finished), 1)
    if not coef or cov < 0.5:
        set_values(finished, None, 0)
        return 0.0, res, cov
    dates = [m["date"] for m in finished]
    refs = [now - dt.timedelta(days=d) for d in range(150, 9, -10)]
    for w in W_GRID:
        set_values(finished, coef, w)
        ll = br = 0.0
        n = 0
        for ref in refs:
            i0 = bisect.bisect_left(dates, ref)
            i1 = bisect.bisect_left(dates, ref + dt.timedelta(days=10))
            model = build_model(finished[:i0], ref)
            if not model:
                continue
            for m in finished[i0:i1]:
                lh, la = lambdas(model, m["hid"], m["aid"])
                ll += m["hg"] * math.log(lh) - lh + m["ag"] * math.log(la) - la
                p25 = 1 - sum(pois(i, lh + la) for i in range(3))
                br += (p25 - (1 if m["hg"] + m["ag"] >= 3 else 0)) ** 2
                n += 1
        if n:
            res[w] = (ll / n, br / n, n)
    best = max(res, key=lambda w: res[w][0]) if res else 0.0
    set_values(finished, coef, best)
    return best, res, cov


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
            vh, va = m.get("vh", m["hg"]), m.get("va", m["ag"])
            na[h] += w1 * vh
            da[h] += w1 * base * ha * dfn[a]
            na[a] += w2 * va
            da[a] += w2 * base / ha * dfn[h]
            nd[h] += w1 * va
            dd[h] += w1 * base / ha * att[a]
            nd[a] += w2 * vh
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
    if matches[-1].get("cup") and CUP_DOM:
        try:
            model["cupx"] = cup_layer(ref)
        except Exception as e:  # noqa
            print("kupa lig gücü hesaplanamadı:", e, flush=True)
    return model


# ------------------------------------------------------------ Avrupa kupaları: lig zorluğu
# Kupa maçında takımın gücü = kendi ligindeki hücum/savunma gücü × ligin Avrupa'daki gücü.
# Lig güçleri, kupalardaki ligler arası maçların sonuçlarından tahmin edilir (gerçek veride
# 298 Avrupa maçında sadece kupa maçlarına dayanan eski yönteme göre belirgin daha iyi tahmin etti).
# Kendi ligi takip edilmeyen takımlar ("diğer") için kupa maçlarından hesaplanan güç kullanılır.
CUP_DOM = {}           # yerel lig -> biten maçlar (tarihe göre sıralı)
CUP_ALL = []           # tüm kupa maçları (biten, sıralı)
CUP_PS = 0.35          # lig gücü için önsel yayılım (log ölçekte)
CUP_MIN_GAMES = 8      # yerel lig gücünün kullanılması için en az maç
_CUP_CACHE = {}


def _week(ref):
    d = (ref - dt.timedelta(days=ref.weekday())).date()
    return dt.datetime(d.year, d.month, d.day, tzinfo=UTC)


def dom_model(slug, r):
    key = ("m", slug, r)
    if key not in _CUP_CACHE:
        fin = CUP_DOM[slug]
        i = bisect.bisect_left([m["date"] for m in fin], r)
        _CUP_CACHE[key] = build_model(fin[:i], r)
    return _CUP_CACHE[key]


def team_leagues(r):
    key = ("tl", r)
    if key not in _CUP_CACHE:
        c = defaultdict(lambda: defaultdict(int))
        for sl, fin in CUP_DOM.items():
            for m in fin:
                if r - dt.timedelta(days=365) <= m["date"] < r:
                    c[m["hid"]][sl] += 1
                    c[m["aid"]][sl] += 1
        _CUP_CACHE[key] = {t: max(cc, key=cc.get) for t, cc in c.items()}
    return _CUP_CACHE[key]


def fit_league_strength(rows):
    """rows: (ağırlık, ev gol, dep gol, ev hücum, ev savunma, dep hücum, dep savunma, ev ligi, dep ligi)."""
    S = defaultdict(float)
    mh = ma = 1.3
    for _ in range(40):
        eh = sum(w * Ah * Da * math.exp(S[Lh] - S[La]) for w, hg, ag, Ah, Dh, Aa, Da, Lh, La in rows)
        ea = sum(w * Aa * Dh * math.exp(S[La] - S[Lh]) for w, hg, ag, Ah, Dh, Aa, Da, Lh, La in rows)
        mh = sum(r[0] * r[1] for r in rows) / max(eh, 1e-9)
        ma = sum(r[0] * r[2] for r in rows) / max(ea, 1e-9)
        g, H = defaultdict(float), defaultdict(float)
        for w, hg, ag, Ah, Dh, Aa, Da, Lh, La in rows:
            if Lh == La:
                continue
            lh = mh * Ah * Da * math.exp(S[Lh] - S[La])
            la = ma * Aa * Dh * math.exp(S[La] - S[Lh])
            d = (hg - lh) - (ag - la)
            g[Lh] += w * d
            g[La] -= w * d
            H[Lh] += w * (lh + la)
            H[La] += w * (lh + la)
        for L in g:
            if L != "diğer":
                S[L] += 0.7 * (g[L] - S[L] / CUP_PS ** 2) / (H[L] + 1 / CUP_PS ** 2)
    return mh, ma, dict(S)


def cup_layer(ref):
    r = _week(ref)
    key = ("cx", r)
    if key in _CUP_CACHE:
        return _CUP_CACHE[key]
    past = [m for m in CUP_ALL if r - dt.timedelta(days=400) <= m["date"] < r]
    if len(past) < 40:
        return None
    tw = time_weights(past, r)
    allm = fit_strength(past, tw)
    tl = team_leagues(r)

    def rate(t):
        L = tl.get(t)
        dm = dom_model(L, r) if L else None
        if dm and dm["games"].get(t, 0) >= CUP_MIN_GAMES and t in dm["att"]:
            return dm["att"][t], dm["dfn"][t], L
        return allm["att"].get(t, NEW_ATT), allm["dfn"].get(t, NEW_DEF), "diğer"
    rows = []
    for w, m in zip(tw, past):
        Ah, Dh, Lh = rate(m["hid"])
        Aa, Da, La = rate(m["aid"])
        rows.append((w, m["hg"], m["ag"], Ah, Dh, Aa, Da, Lh, La))
    mh, ma, S = fit_league_strength(rows)
    out = {"mh": mh, "ma": ma, "S": S, "rate": rate}
    _CUP_CACHE[key] = out
    return out


def lambdas(model, h, a):
    if not model:
        return None
    cx = model.get("cupx")
    if cx:
        Ah, Dh, Lh = cx["rate"](h)
        Aa, Da, La = cx["rate"](a)
        S = cx["S"]
        lam_h = cx["mh"] * Ah * Da * math.exp(S.get(Lh, 0) - S.get(La, 0))
        lam_a = cx["ma"] * Aa * Dh * math.exp(S.get(La, 0) - S.get(Lh, 0))
        return min(max(lam_h, 0.15), 5.0), min(max(lam_a, 0.15), 5.0)
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
        "o35": S(lambda i, j: i + j >= 4), "o45": S(lambda i, j: i + j >= 5),
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
    r["ih05"] = sum(p for (i, j), p in g1.items() if i >= 1)
    r["ia05"] = sum(p for (i, j), p in g1.items() if j >= 1)
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


# ------------------------------------------------------------ oran arşivi ve orana göre benzer maçlar
# ESPN maç bitince oranı siler; bu yüzden maç öncesi oranlar her gün arşive yazılır. Arşivde yeterli
# sonuçlanmış maç birikince "benzer maçlar" oran profili (MS 1-X-2 ve 2.5 Alt/Üst) en yakın maçlardan seçilir.
ODDS_FILE = "data/oran_arsiv.json"
ODDS_MIN = 400          # orana göre benzer maç için arşivde gereken en az sonuçlanmış maç
ODDS_KEEP_DAYS = 400
ODDS_ARCH = {}


def load_odds():
    global ODDS_ARCH
    try:
        with open(ODDS_FILE, encoding="utf-8") as f:
            ODDS_ARCH = json.load(f)
    except Exception:  # noqa
        ODDS_ARCH = {}
    return ODDS_ARCH


def odds_feat(o):
    """Oranlardan piyasa ihtimalleri: (ev, deplasman, 2.5 üst ya da None)."""
    try:
        q = [1 / o["1"], 1 / o["X"], 1 / o["2"]]
    except (KeyError, TypeError, ZeroDivisionError):
        return None
    t = sum(q)
    ov = None
    if o.get("line") == 2.5 and o.get("over") and o.get("under"):
        a, b_ = 1 / o["over"], 1 / o["under"]
        ov = a / (a + b_)
    return q[0] / t, q[2] / t, ov


def odds_neighbors(o, k=SIM_K):
    f = odds_feat(o) if o else None
    if not f:
        return None
    pool = []
    for mid, e in ODDS_ARCH.items():
        if not e.get("res"):
            continue
        g = odds_feat(e["o"])
        if not g:
            continue
        d = (f[0] - g[0]) ** 2 + (f[1] - g[1]) ** 2
        d += (f[2] - g[2]) ** 2 if f[2] is not None and g[2] is not None else 0.01
        pool.append((d, e))
    if len(pool) < ODDS_MIN:
        return None
    pool.sort(key=lambda x: x[0])
    out = []
    for _, e in pool[:k]:
        hg, ag, h1, a1 = e["res"]
        out.append({"hg": hg, "ag": ag, "ht": (h1, a1) if h1 is not None else None,
                    "home": e["h"], "away": e["a"], "date": dt.datetime.fromisoformat(e["k"])})
    return out


def update_odds_archive(leagues, now):
    arch = ODDS_ARCH
    for L in leagues:
        for c in L.get("cards", []):
            o = c.get("odds")
            if c["state"] == "pre" and c["kick"] > now and o and odds_feat(o):
                e = arch.setdefault(c["id"], {})
                e.update({"k": c["kick"].isoformat(), "lg": L["name"], "h": c["home"], "a": c["away"],
                          "o": {k: o[k] for k in ("1", "X", "2", "line", "over", "under") if k in o}})
        for mid, r in L.get("results", {}).items():
            if mid in arch and not arch[mid].get("res") and r[0] is not None:
                arch[mid]["res"] = list(r)
    cut = (now - dt.timedelta(days=ODDS_KEEP_DAYS)).isoformat()
    for mid in [m for m, e in arch.items() if e["k"] < cut]:
        del arch[mid]
    with open(ODDS_FILE, "w", encoding="utf-8") as f:
        json.dump(arch, f, ensure_ascii=False, separators=(",", ":"))


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


# ------------------------------------------------------------ gol raporu (kontrol listesi)
GOAL_MARKETS = [
    ("iy05", "İY 0.5 Üst"), ("iy15", "İY 1.5 Üst"), ("iykg", "İY KG Var"),
    ("o15", "1.5 Üst"), ("o25", "2.5 Üst"), ("o35", "3.5 Üst"), ("o45", "4.5 Üst"),
    ("btts", "KG Var"), ("u25", "2.5 Alt"),
]
TEAM_MARKETS = [("h05", "Ev 0.5 Üst"), ("a05", "Dep 0.5 Üst"), ("h15", "Ev 1.5 Üst"), ("a15", "Dep 1.5 Üst"),
                ("ih05", "Ev İY 0.5 Üst"), ("ia05", "Dep İY 0.5 Üst")]
# takım golü bahsi -> (hücum eden taraf, gol eşiği, ilk yarı mı)
TEAM_KEY = {"h05": ("h", 1, False), "a05": ("a", 1, False), "h15": ("h", 2, False), "a15": ("a", 2, False),
            "ih05": ("h", 1, True), "ia05": ("a", 1, True)}
RP_MARKETS = GOAL_MARKETS + TEAM_MARKETS + [("ms1", "MS 1"), ("ms2", "MS 2")]
GM_LABEL = dict(RP_MARKETS)
MAIN_EXCLUDE = {"o15", "iy05", "h05", "a05"}   # oranı çok düşük; günün önerisi olarak seçilmez
TIER_NAME = {2: "GÜÇLÜ", 1: "ORTA", 0: "ZAYIF"}
RP_MIN_CHECKS = 5
MAIN_MIN_P = 0.55        # günün önerisi için en düşük model olasılığı
ALT_MIN_P = 0.40         # ikinci öneri için en düşük model olasılığı
CLASH = {"o25": {"u25"}, "o35": {"u25"}, "o45": {"u25"}, "u25": {"o25", "o35", "o45"},
         "ms1": {"ms2"}, "ms2": {"ms1"}}
TRUST = None             # bahis türü + seviye bazında geçmiş başarı (main() içinde doldurulur)
TRUST_EVAL = None
GLOBAL_TH = None         # tüm liglerden birleşik takım geçmişi (Avrupa kupaları için)
FETCHED = {}             # önceden çekilmiş lig verisi (kupalar)
PREV_SNAPSHOT = None
MACS_BY_ID = {}
TRUST_MIN_N = 25
TRUST_LIFT = 0.03        # geçmişte ortalamadan en az 3 puan iyi olmalı


def gev(key, gf, ga, gf1, ga1):
    """Bir maç (ya da takım satırı) için gol bahsi gerçekleşti mi? İY skoru yoksa None."""
    if key == "o15":
        return gf + ga >= 2
    if key == "o25":
        return gf + ga >= 3
    if key == "o35":
        return gf + ga >= 4
    if key == "o45":
        return gf + ga >= 5
    if key == "u25":
        return gf + ga <= 2
    if key == "btts":
        return gf > 0 and ga > 0
    if key == "ms1":
        return gf > ga
    if key == "ms2":
        return gf < ga
    if key in TEAM_KEY:
        side, n, half = TEAM_KEY[key]
        if half:
            if gf1 is None or ga1 is None:
                return None
            g = gf1 if side == "h" else ga1
        else:
            g = gf if side == "h" else ga
        return g >= n
    if gf1 is None or ga1 is None:
        return None
    if key == "iy05":
        return gf1 + ga1 >= 1
    if key == "iy15":
        return gf1 + ga1 >= 2
    if key == "iykg":
        return gf1 > 0 and ga1 > 0
    return None


def m_ev(key, m):
    ht = m.get("ht")
    return gev(key, m["hg"], m["ag"], ht[0] if ht else None, ht[1] if ht else None)


def model_p(key, r):
    if key == "u25":
        return 1 - r["o25"]
    if key == "ms1":
        return r["p1"]
    if key == "ms2":
        return r["p2"]
    return r.get(key)


def ppg(rows):
    return sum(3 if x[1] > x[2] else (1 if x[1] == x[2] else 0) for x in rows) / len(rows) if rows else None


def team_val(key, x, side):
    """Takım satırında (x: takımın gözünden) takım golü bahsi: hücum eden tarafsa attığı, değilse yediği gol."""
    att, n, half = TEAM_KEY[key]
    i = (3 if half else 1) if side == att else (4 if half else 2)
    return None if x[i] is None else x[i] >= n


def rows_rate(key, rows, side="h"):
    if key in TEAM_KEY:
        v = [team_val(key, x, side) for x in rows]
        v = [x for x in v if x is not None]
        return sum(v), len(v)
    if key in ("ms1", "ms2"):
        want_win = (key == "ms1") == (side == "h")
        v = [(x[1] > x[2]) if want_win else (x[1] < x[2]) for x in rows]
        return sum(v), len(v)
    v = [gev(key, x[1], x[2], x[3], x[4]) for x in rows]
    v = [x for x in v if x is not None]
    return sum(v), len(v)


def rows_mean(rows, i):
    v = [x[i] for x in rows if x[i] is not None]
    return sum(v) / len(v) if v else None


def rapor_ctx(past, ref):
    recent = [m for m in past if m["date"] >= ref - dt.timedelta(days=365)] or past
    # kupalarda ön eleme maçları (Temmuz-Ağustos) lig ortalamasını şişirir: ortalamaya katılmaz
    rc = [m for m in recent if not (m.get("cup") and m["date"].month in (7, 8))]
    if len(rc) >= 60:
        recent = rc
    base = {}
    for key, _ in RP_MARKETS:
        v = [m_ev(key, m) for m in recent]
        v = [x for x in v if x is not None]
        base[key] = sum(v) / len(v) if len(v) >= 30 else None
    tot = [m["hg"] + m["ag"] for m in recent]
    tot1 = [m["ht"][0] + m["ht"][1] for m in recent if m.get("ht")]
    pairs = defaultdict(list)
    for m in past:
        pairs[frozenset((m["hid"], m["aid"]))].append(m)
    xs = [xg_of(m, m.get("_coef")) for m in recent]
    xs = [a + b for a, b in xs if a is not None]
    return {"base": base, "avg": sum(tot) / len(tot) if tot else None,
            "avg1": sum(tot1) / len(tot1) if tot1 else None, "pairs": pairs, "th": team_history(past),
            "avgx": sum(xs) / len(xs) if len(xs) >= 30 else None, "gmb": gm_base(recent)}


GI_BINS = [(1, 15), (16, 30), (31, 45), (46, 60), (61, 75), (76, 120)]
GI_LABEL = ["1-15", "16-30", "31-45", "46-60", "61-75", "76-90"]
GI_N = 15          # gol dakikası analizinde takım başına son maç sayısı


def gi_bin(mn):
    mn = abs(mn)
    for i, (a, b) in enumerate(GI_BINS):
        if a <= mn <= b:
            return i
    return len(GI_BINS) - 1


def gm_stats(rows):
    """Gol dakikalı maçlardan (takımın gözünden işaretli listeler) dakika ve maç içi durum istatistikleri.
    rows: [(attığı, yediği, [işaretli dakikalar]), ...]"""
    rs = [r for r in rows if r[2] is not None]
    n = len(rs)
    if n == 0:
        return None
    f, a, anyg = [0] * 6, [0] * 6, [0] * 6
    for _, _, g in rs:
        seen = set()
        for x in g:
            i = gi_bin(x)
            (f if x > 0 else a)[i] += 1
            seen.add(i)
        for i in seen:
            anyg[i] += 1
    wg = [r for r in rs if r[2]]
    sf = [r for r in wg if r[2][0] > 0]          # ilk golü attığı
    cf = [r for r in wg if r[2][0] < 0]          # ilk golü yediği

    def rate(lst, fn):
        return (sum(1 for r in lst if fn(r)), len(lst))
    return {
        "n": n, "f": f, "a": a, "any": anyg,
        "early": rate(rs, lambda r: any(abs(x) <= 30 for x in r[2])),
        "late": rate(rs, lambda r: any(abs(x) >= 76 for x in r[2])),
        "open": rate(wg, lambda r: len(r[2]) >= 3),                    # ilk golden sonra 2+ gol daha
        "sfwin": rate(sf, lambda r: r[0] > r[1]),                      # öne geçince kazandı
        "reply": rate(cf, lambda r: any(x > 0 for x in r[2])),          # geriye düşünce gol attı
        "comeback": rate(cf, lambda r: r[0] >= r[1]),                  # geriye düşünce puan aldı
    }


def team_gm(rows):
    return gm_stats([(x[1], x[2], x[13]) for x in rows if len(x) > 13])


def rr(t):
    return t[0] / t[1] if t and t[1] else None


def gm_base(recent):
    """Lig tabanı: maç bazında erken/geç gol, açılma; takım bazında öne geçince kazanma, geri dönüş."""
    ms = [m for m in recent if m.get("gm") is not None]
    if len(ms) < 60:
        return None
    rows = [(m["hg"], m["ag"], m["gm"]) for m in ms] + [(m["ag"], m["hg"], [-x for x in m["gm"]]) for m in ms]
    st = gm_stats(rows)
    half = gm_stats([(m["hg"], m["ag"], m["gm"]) for m in ms])
    return {"n": len(ms), "early": rr(half["early"]), "late": rr(half["late"]), "open": rr(half["open"]),
            "sfwin": rr(st["sfwin"]), "reply": rr(st["reply"]), "comeback": rr(st["comeback"]),
            "f": [x / len(ms) for x in half["f"]], "a": [x / len(ms) for x in half["a"]]}


def xmean(rows, i, minn=6):
    v = [x[i] for x in rows if len(x) > i and x[i] is not None]
    return sum(v) / len(v) if len(v) >= minn else None


def rapor_eval(ctx, m, r, nb, hn, an):
    """Her gol bahsi için 8 maddelik kontrol listesi, seviye ve günün önerisi."""
    th = ctx["th"]
    hr, ar = th.get(m["hid"], []), th.get(m["aid"], [])
    h10, a10 = hr[-10:], ar[-10:]
    hv = [x for x in hr if x[5]][-5:]
    av = [x for x in ar if not x[5]][-5:]
    h2h = ctx["pairs"].get(frozenset((m["hid"], m["aid"])), [])[-4:]
    out = {}
    for key, label in RP_MARKETS:
        base, p = ctx["base"].get(key), model_p(key, r)
        if base is None or p is None:
            continue
        checks = []

        def add(ok, text):
            checks.append((bool(ok), text))
        add(p >= base + 0.08, f"Model: %{p * 100:.0f} (lig ortalaması %{base * 100:.0f})")
        ms = key in ("ms1", "ms2")
        for rows, who, minn, side in ((h10, f"{hn} son maçları", 6, "h"), (a10, f"{an} son maçları", 6, "a"),
                                      (hv, f"{hn} evdeki son maçları", 4, "h"),
                                      (av, f"{an} dışarıdaki son maçları", 4, "a")):
            k, n = rows_rate(key, rows, side)
            if n >= minn:
                if ms:
                    win = (key == "ms1") == (side == "h")
                    word = "kazandı" if win else "kaybetti"
                    add(k / n >= base + 0.10, f"{who}: {n} maçta {k} {word} (%{k / n * 100:.0f})")
                elif key in TEAM_KEY:
                    att, ng, half = TEAM_KEY[key]
                    word = ("attığı" if side == att else "yediği")
                    add(k / n >= base + 0.10, f"{who}: {'ilk yarıda ' if half else ''}{'2+ ' if ng == 2 else ''}gol "
                                              f"{word} maç {k}/{n} (%{k / n * 100:.0f})")
                else:
                    add(k / n >= base + 0.10, f"{who}: {k}/{n} (%{k / n * 100:.0f})")
        nk = [m_ev(key, x) for x in nb]
        nk = [x for x in nk if x is not None]
        if len(nk) >= 30:
            k = sum(nk)
            lab_ = f" ({ctx['nb_lab']})" if ctx.get("nb_lab") else ""
            add(k / len(nk) >= base + 0.06, f"Benzer {len(nk)} maç{lab_}: {k}/{len(nk)} (%{k / len(nk) * 100:.0f})")
        if ms:   # aralarındaki maçlar: bugünkü ev sahibine göre
            hk = []
            for x in h2h:
                hg_, ag_ = (x["hg"], x["ag"]) if x["hid"] == m["hid"] else (x["ag"], x["hg"])
                hk.append(hg_ > ag_ if key == "ms1" else hg_ < ag_)
        elif key in TEAM_KEY:   # bugünkü ev sahibine göre çevir
            hk = []
            for x in h2h:
                sw = x["hid"] != m["hid"]
                hg_, ag_ = (x["ag"], x["hg"]) if sw else (x["hg"], x["ag"])
                ht_ = x.get("ht")
                h1_, a1_ = ((ht_[1], ht_[0]) if sw else (ht_[0], ht_[1])) if ht_ else (None, None)
                hk.append(gev(key, hg_, ag_, h1_, a1_))
        else:
            hk = [m_ev(key, x) for x in h2h]
        hk = [x for x in hk if x is not None]
        if len(hk) >= 2:
            k = sum(hk)
            add(k / len(hk) >= max(base, 0.5), f"Aralarındaki son {len(hk)} maç: {k}/{len(hk)}")
        if ms and len(h10) >= 6 and len(a10) >= 6:
            ph, pa = ppg(h10), ppg(a10)
            diff = ph - pa if key == "ms1" else pa - ph
            add(diff >= 0.5, f"Son 10 maç puan ortalaması: {hn} {ph:.1f}, {an} {pa:.1f}")
        elif key in ("o15", "o25", "o35", "o45", "u25") and ctx["avg"]:
            parts = [rows_mean(h10, 1), rows_mean(a10, 2), rows_mean(a10, 1), rows_mean(h10, 2)]
            if None not in parts:
                exp = (parts[0] + parts[1]) / 2 + (parts[2] + parts[3]) / 2
                ok = exp <= ctx["avg"] - 0.25 if key == "u25" else exp >= ctx["avg"] + 0.25
                add(ok, f"Son maçlara göre beklenen toplam gol {exp:.1f} (lig {ctx['avg']:.1f})")
        elif key in ("iy05", "iy15") and ctx["avg1"]:
            parts = [rows_mean(h10, 3), rows_mean(a10, 4), rows_mean(a10, 3), rows_mean(h10, 4)]
            if None not in parts:
                exp = (parts[0] + parts[1]) / 2 + (parts[2] + parts[3]) / 2
                add(exp >= ctx["avg1"] + 0.15, f"Son maçlara göre ilk yarı gol beklentisi {exp:.1f} (lig {ctx['avg1']:.1f})")
        elif key in TEAM_KEY and len(h10) >= 6 and len(a10) >= 6:
            att, ng, half = TEAM_KEY[key]
            ar_, dr_ = (h10, a10) if att == "h" else (a10, h10)
            an_, dn_ = (hn, an) if att == "h" else (an, hn)
            gi_, ci_ = (3, 4) if half else (1, 2)
            f_, c_ = rows_mean(ar_, gi_), rows_mean(dr_, ci_)
            lavg = (ctx["avg1"] if half else ctx["avg"])
            if f_ is not None and c_ is not None and lavg:
                ex = (f_ + c_) / 2
                add(ex >= lavg / 2 * (1.15 if ng == 1 else 1.3),
                    f"Son maçlara göre {an_} {'ilk yarı ' if half else ''}gol beklentisi {ex:.1f} "
                    f"({an_} maç başı {f_:.1f} attı, {dn_} {c_:.1f} yedi; lig takım ort. {lavg / 2:.1f})")
        elif key == "btts" and len(h10) >= 6 and len(a10) >= 6:
            k1 = sum(1 for x in h10 if x[1] > 0)
            k2 = sum(1 for x in a10 if x[1] > 0)
            add(k1 / len(h10) >= 0.7 and k2 / len(a10) >= 0.7,
                f"Gol attığı maç: {hn} {k1}/{len(h10)}, {an} {k2}/{len(a10)}")
        ax = ctx.get("avgx")
        if ax:
            hxf, hxa, axf, axa = xmean(h10, 7), xmean(h10, 8), xmean(a10, 7), xmean(a10, 8)
            if None not in (hxf, hxa, axf, axa):
                if key in ("o25", "o35", "o45", "u25"):
                    ex = (hxf + axa) / 2 + (axf + hxa) / 2
                    ok = ex <= ax - 0.25 if key == "u25" else ex >= ax + 0.25
                    add(ok, f"Şutlara göre beklenen toplam gol {ex:.1f} (lig {ax:.1f})")
                elif key in TEAM_KEY and not TEAM_KEY[key][2]:
                    att = TEAM_KEY[key][0]
                    ex = (hxf + axa) / 2 if att == "h" else (axf + hxa) / 2
                    nm_ = hn if att == "h" else an
                    add(ex >= ax / 2 * (1.1 if TEAM_KEY[key][1] == 1 else 1.3),
                        f"Şutlara göre {nm_} beklenen gol {ex:.1f} (takım ort. {ax / 2:.1f})")
                elif key == "btts":
                    eh, ea = (hxf + axa) / 2, (axf + hxa) / 2
                    add(min(eh, ea) >= ax / 2 * 0.95,
                        f"Şutlara göre beklenen gol: {hn} {eh:.1f}, {an} {ea:.1f} (takım ort. {ax / 2:.1f})")
                elif ms:
                    dh, da = hxf - hxa, axf - axa
                    diff = dh - da if key == "ms1" else da - dh
                    add(diff >= 0.5, f"Şut üstünlüğü (maç başı beklenen gol farkı): {hn} {dh:+.1f}, {an} {da:+.1f}")
        if key in ("iy05", "iy15", "iykg") and ctx["avg1"] and ctx["avg"]:
            rows1 = [x for x in h10 + a10 if x[3] is not None]
            g_all = sum(x[1] + x[2] for x in rows1)
            if len(rows1) >= 12 and g_all >= 10:
                sh = sum(x[3] + x[4] for x in rows1) / g_all
                lsh = ctx["avg1"] / ctx["avg"]
                add(sh >= lsh + 0.04, f"İki takımın son maçlarında gollerin %{sh * 100:.0f}'i ilk yarıda (lig %{lsh * 100:.0f})")
        if key == "iykg":
            h1 = [x for x in h10 if x[3] is not None]
            a1 = [x for x in a10 if x[3] is not None]
            if len(h1) >= 6 and len(a1) >= 6:
                k1 = sum(1 for x in h1 if x[3] > 0)
                k2 = sum(1 for x in a1 if x[3] > 0)
                add(k1 / len(h1) >= 0.45 and k2 / len(a1) >= 0.45,
                    f"İlk yarıda gol attığı maç: {hn} {k1}/{len(h1)}, {an} {k2}/{len(a1)}")
        # Gol dakikası / maç içi tepki maddeleri: geri testte isabeti artırmadığı için puana sayılmaz, bilgi olarak gösterilir
        infos = []

        def note(ok, text):
            infos.append((bool(ok), text))
        gb = ctx.get("gmb")
        if gb:
            hs_, as_ = team_gm(hr[-GI_N:]), team_gm(ar[-GI_N:])
            if hs_ and as_ and hs_["n"] >= 8 and as_["n"] >= 8:
                def cmb(k):
                    a_, b_ = hs_[k], as_[k]
                    return (a_[0] + b_[0]) / (a_[1] + b_[1]) if a_[1] + b_[1] else None
                if key in ("iy05", "iy15", "iykg") and gb["early"]:
                    v = cmb("early")
                    note(v is not None and v >= gb["early"] + 0.08,
                        f"İlk 30 dakikada gol olan maç: {hn} {hs_['early'][0]}/{hs_['early'][1]}, "
                        f"{an} {as_['early'][0]}/{as_['early'][1]} (lig %{gb['early'] * 100:.0f})")
                elif key in ("o25", "o35", "o45", "u25") and gb["open"]:
                    v = cmb("open")
                    if v is not None and hs_["open"][1] + as_["open"][1] >= 12:
                        ok = v <= gb["open"] - 0.08 if key == "u25" else v >= gb["open"] + 0.08
                        note(ok, f"İlk golden sonra 2+ gol daha gelen maç: {hn} {hs_['open'][0]}/{hs_['open'][1]}, "
                                f"{an} {as_['open'][0]}/{as_['open'][1]} (lig %{gb['open'] * 100:.0f})")
                elif key == "btts" and gb["reply"]:
                    a_, b_ = hs_["reply"], as_["reply"]
                    if a_[1] >= 3 and b_[1] >= 3:
                        note(a_[0] / a_[1] >= gb["reply"] and b_[0] / b_[1] >= gb["reply"],
                            f"Geriye düşünce gol attığı maç: {hn} {a_[0]}/{a_[1]}, {an} {b_[0]}/{b_[1]} "
                            f"(lig %{gb['reply'] * 100:.0f})")
                elif ms and gb["sfwin"]:
                    fav, opp = (hs_, as_) if key == "ms1" else (as_, hs_)
                    fn_, on_ = (hn, an) if key == "ms1" else (an, hn)
                    if fav["sfwin"][1] >= 3 and opp["comeback"][1] >= 3:
                        note(rr(fav["sfwin"]) >= gb["sfwin"] and rr(opp["comeback"]) <= gb["comeback"],
                            f"{fn_} öne geçince kazandı {fav['sfwin'][0]}/{fav['sfwin'][1]}; "
                            f"{on_} geriye düşünce puan aldı {opp['comeback'][0]}/{opp['comeback'][1]} "
                            f"(lig %{gb['sfwin'] * 100:.0f} / %{gb['comeback'] * 100:.0f})")
        tot = len(checks)
        okc = sum(1 for ok, _ in checks if ok)
        ratio = okc / tot if tot else 0
        tier = 0
        if tot >= RP_MIN_CHECKS and checks[0][0]:
            tier = 2 if ratio >= 0.8 else (1 if ratio >= 0.6 else 0)
        out[key] = {"p": p, "base": base, "checks": checks, "info": infos, "ok": okc, "tot": tot, "tier": tier,
                    "score": ratio + (p - base)}
    # Günün önerisi: kriterleri tutan, olması muhtemel (model en az %55) ve geçmişte işe yaramış bahis türü
    def ok_trust(k, tier):
        if TRUST is None:
            return True
        t = TRUST.get((k, tier))
        return bool(t and t["ok"])
    cand = sorted([(v["tier"], v["score"], k) for k, v in out.items()
                   if k not in MAIN_EXCLUDE and v["tier"] >= 1 and ok_trust(k, v["tier"])], reverse=True)
    main = next((k for _, _, k in cand if out[k]["p"] >= MAIN_MIN_P), None)
    alt = None
    if main:
        clash = CLASH.get(main, set()) | {main}
        alt = next((k for _, _, k in cand if k not in clash and out[k]["p"] >= ALT_MIN_P), None)
    return {"m": out, "main": main, "alt": alt}


def trust_from(rows):
    """rows: [(rp, ...)] -> {(bahis, seviye): {hit, n, base, ok}}; seviye 1/2 için geçmiş isabet."""
    tot = defaultdict(lambda: [0, 0])
    st = defaultdict(lambda: [0, 0])
    for rp in rows:
        for k, v in rp.items():
            if v[1] is None:
                continue
            tot[k][0] += v[1]
            tot[k][1] += 1
            if v[0] in (1, 2):
                st[(k, v[0])][0] += v[1]
                st[(k, v[0])][1] += 1
    out = {}
    for (k, t), (h, n) in st.items():
        base = tot[k][0] / tot[k][1] if tot[k][1] else 0
        out[(k, t)] = {"hit": h / n if n else 0, "n": n, "base": base,
                       "ok": n >= TRUST_MIN_N and h / n >= base + TRUST_LIFT}
    return out


def pick_main(rp, trust):
    cand = sorted([(v[0], v[3], k) for k, v in rp.items()
                   if k not in MAIN_EXCLUDE and v[0] >= 1 and (trust.get((k, v[0])) or {}).get("ok")], reverse=True)
    return next((k for _, _, k in cand if rp[k][2] >= MAIN_MIN_P), None)


def standings(season):
    t = defaultdict(lambda: {"p": 0, "pl": 0, "gf": 0, "ga": 0})
    for m in season:
        for tid, gf, ga in ((m["hid"], m["hg"], m["ag"]), (m["aid"], m["ag"], m["hg"])):
            x = t[tid]
            x["pl"] += 1
            x["gf"] += gf
            x["ga"] += ga
            x["p"] += 3 if gf > ga else (1 if gf == ga else 0)
    order = sorted(t, key=lambda k: (-t[k]["p"], -(t[k]["gf"] - t[k]["ga"]), -t[k]["gf"]))
    return t, {k: i + 1 for i, k in enumerate(order)}, len(order)


def pos_tag(rank, n, pl):
    if not rank or pl < 4:
        return "sezon başı"
    if rank <= 3:
        return "zirve yarışında"
    if rank <= max(4, n // 4):
        return "üst sıralarda"
    if rank >= n - 2:
        return "düşme hattında"
    return "orta sıralarda"


def team_ctx(tid, ctx, table, rank, n):
    rows = ctx["th"].get(tid, [])
    l10 = rows[-10:]
    form = "".join("G" if x[1] > x[2] else ("B" if x[1] == x[2] else "M") for x in rows[-5:][::-1])  # en yeni önce
    t = table.get(tid, {"p": 0, "pl": 0})
    return {"rank": rank.get(tid), "n": n, "pts": t["p"], "pl": t["pl"], "form": form,
            "tag": pos_tag(rank.get(tid), n, t["pl"]),
            "gf": rows_mean(l10, 1), "ga": rows_mean(l10, 2), "gf1": rows_mean(l10, 3), "ga1": rows_mean(l10, 4),
            "xf": xmean(l10, 7), "xa": xmean(l10, 8), "sf": xmean(l10, 9), "sa": xmean(l10, 10),
            "cf": xmean(l10, 11), "ca": xmean(l10, 12),
            "luck": (sum(x[1] for x in l10 if x[7] is not None) - sum(x[7] for x in l10 if x[7] is not None))
            if sum(1 for x in l10 if x[7] is not None) >= 6 else None,
            "last5": [(x[6], x[1], x[2], x[5]) for x in rows[-5:]][::-1]}


def rest_days(tid, kick, th):
    rows = (th or {}).get(tid) or []
    prev = [x[0] for x in rows if x[0] < kick - dt.timedelta(hours=3)]
    return (kick - max(prev)).days if prev else None


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
def team_history(matches, coef=None):
    """Takım satırı: (tarih, attı, yedi, İY attı, İY yedi, evde mi, rakip,
    şut-kalitesi lehine, aleyhine, isabetli şut lehine, aleyhine, korner lehine, aleyhine,
    gol dakikaları: attığı +dk, yediği -dk)."""
    th = defaultdict(list)
    for m in matches:
        ht = m.get("ht")
        s = m.get("st") or {}
        xh, xa = xg_of(m, coef or m.get("_coef"))
        th[m["hid"]].append((m["date"], m["hg"], m["ag"],
                             ht[0] if ht else None, ht[1] if ht else None, True, m["away"],
                             xh, xa, s.get("hsot"), s.get("asot"), s.get("hc"), s.get("ac"),
                             m.get("gm")))
        th[m["aid"]].append((m["date"], m["ag"], m["hg"],
                             ht[1] if ht else None, ht[0] if ht else None, False, m["home"],
                             xa, xh, s.get("asot"), s.get("hsot"), s.get("ac"), s.get("hc"),
                             [-x for x in m["gm"]] if m.get("gm") is not None else None))
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
        rctx = rapor_ctx(matches[:idx], ref)
        plams = [(lambdas(model, x["hid"], x["aid"]), x) for x in matches[:idx]]
        for m in matches[idx:]:
            if m["date"].date() != d:
                continue
            lam = lambdas(model, m["hid"], m["aid"])
            hl = half_lams(model, m["hid"], m["aid"], *lam)
            r0 = analyze(*lam, rho=model["rho"], half=hl, joint=False)
            ev = rapor_eval(rctx, m, r0, neighbors(plams, *lam), m["home"], m["away"])
            out.append({"date": ref, "lam": lam, "mu": mus(model), "rho": model["rho"],
                        "sh": (hl[0] / lam[0], hl[1] / lam[1]) if hl else None,
                        "hg": m["hg"], "ag": m["ag"], "m": m,
                        "rp": {k: (v["tier"], m_ev(k, m), v["p"], v["score"]) for k, v in ev["m"].items()},
                        "rpmain": ev["main"]})
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
            "avg90": None, "bt": [], "model": None, "results": {}, "rev": None, "kc": None,
            "rp_bt": [], "rbase": {}, "xw": 0.0, "xwres": {}, "xcov": 0.0, "xcoef": None}
    try:
        finished, allm = FETCHED.pop(slug) if slug in FETCHED else fetch_league(slug, now)
    except Exception as e:  # noqa
        info["err"] = f"Veri alınamadı: {e}"
        return info
    if slug.startswith("uefa."):
        for m in allm:
            m["cup"] = True
    info["results"] = {m["id"]: [m["hg"], m["ag"]] + (list(m["ht"]) if m.get("ht") else [None, None])
                       for m in finished}
    bf = dt.datetime.fromisoformat(BET_FROM).replace(tzinfo=TR)
    info["allm_bet"] = [m for m in allm if m["date"] >= bf]
    info["allm"] = allm
    info["nall"] = len(allm)
    d0, d1 = day_window(now)
    stale = [m for m in allm if not m["done"] and m["date"] < now - dt.timedelta(hours=6)
             and m["date"] > now - dt.timedelta(days=21)]
    recent_done = [m for m in finished if m["date"] > now - dt.timedelta(days=21)]
    if len(stale) >= 5 and len(stale) > len(recent_done):
        info["err"] = (f"ESPN bu ligin sonuçlarını güncellemiyor (son 3 haftada {len(stale)} maç "
                       f"sonuçsuz, {len(recent_done)} maç sonuçlu)")
        return info
    past = [m for m in finished if m["date"] < d0]      # bugünün sonuçları modele sızmasın
    info["nfin"] = len(past)
    info["ny"] = sum(1 for m in past if m["date"] >= d0 - dt.timedelta(days=1))
    if len(past) < 30:
        info["err"] = f"Yetersiz geçmiş veri ({len(past)} maç)"
        return info

    c90 = [m for m in past if m["date"] >= now - dt.timedelta(days=90)]
    if c90:
        info["avg90"] = sum(m["hg"] + m["ag"] for m in c90) / len(c90)

    coef = xg_coef(past)
    for m in finished:
        m["_coef"] = coef
    w, wres, cov = choose_w(finished, now, coef)
    info.update(xw=w, xwres=wres, xcov=cov, xcoef=coef)
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
    info["rp_bt"] = [(x["rp"], x["rpmain"], x["date"]) for x in raw if "rp" in x]
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
    # Değerli oranı sadece modelin bu ligde lig ortalamasını geçtiği bahis türlerinde göster
    def skill(st):
        return (st or {}).get("skill") or 0.0
    trusted = set()
    if skill(ms_stats(info["bt"])) > 0:
        trusted |= {"1", "X", "2"}
    for ln, key in LINE_KEY.items():
        if skill(market_stats(info["bt"], key)) > 0:
            trusted |= {f"o{ln}", f"u{ln}"}
    info["trusted"] = trusted
    mu = mus(model)
    past_lams = [(lambdas(model, m["hid"], m["aid"]), m) for m in past]
    rctx = rapor_ctx(past, now)
    if info["slug"].startswith("uefa.") and GLOBAL_TH:
        rctx["th"] = GLOBAL_TH           # kupada takımların kendi ligindeki maçları da forma dahil
    table, rank, nteams = standings([m for m in past if m["date"] >= ss])
    info["rbase"] = rctx["base"]
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
        nb = odds_neighbors(m.get("odds"))
        rctx["nb_lab"] = "orana göre" if nb else ""
        if not nb:
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
            "hid": m["hid"], "aid": m["aid"],
            "odds": m.get("odds"),
            "vb": [],
            "simst": ss_, "surprise": surprise,
            "time": m["date"].astimezone(TR).strftime("%H:%M"),
            "day": m["date"].astimezone(TR).strftime("%d.%m"),
            "home": m["home"], "away": m["away"], "lam": lam, "r": r, "low": low,
            "state": m["state"], "score": (m["hg"], m["ag"]) if m["done"] else None,
            "hs": tstat(m["hid"], True), "as": tstat(m["aid"], False),
            "sim": [sim_text(x) for x in nb[:5]],
            "rapor": rapor_eval(rctx, m, r, nb, m["home"], m["away"]),
            "tsc": {"h": score_freq(rctx["th"].get(m["hid"], [])[-10:]), "a": score_freq(rctx["th"].get(m["aid"], [])[-10:])},
            "gi": {"h": team_gm(rctx["th"].get(m["hid"], [])[-GI_N:]), "a": team_gm(rctx["th"].get(m["aid"], [])[-GI_N:]),
                   "lg": rctx.get("gmb")},
            "tctx": {"h": dict(team_ctx(m["hid"], rctx, table, rank, nteams),
                               rest=rest_days(m["hid"], m["date"], GLOBAL_TH or rctx["th"])),
                     "a": dict(team_ctx(m["aid"], rctx, table, rank, nteams),
                               rest=rest_days(m["aid"], m["date"], GLOBAL_TH or rctx["th"]))},
            "lavg": rctx["avg"], "ht": m.get("ht"),
        })
    info["cards"].sort(key=lambda c: (c["day"], c["time"]))
    return info


# ------------------------------------------------------------ kayıt ve karne
PRED_KEYS = ["p1", "px", "p2", "o15", "o25", "o35", "o45", "btts", "iy05", "iy15", "iykg", "p21", "p12",
             "h05", "a05", "h15", "a15", "ih05", "ia05"]


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
                "rp": ({"c": c["rapor"]["main"], "t": c["rapor"]["m"][c["rapor"]["main"]]["tier"]}
                       if c.get("rapor") and c["rapor"]["main"] else None),
                "rpm": ({k: v["tier"] for k, v in c["rapor"]["m"].items()} if c.get("rapor") else {}),
                "rp2": ({"c": c["rapor"]["alt"], "t": c["rapor"]["m"][c["rapor"]["alt"]]["tier"]}
                        if c.get("rapor") and c["rapor"].get("alt") else None),
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
    if key in TEAM_KEY:
        return gev(key, hg, ag, h1, a1)
    if key == "u25":
        return hg + ag <= 2
    if key == "ms1":
        return hg > ag
    if key == "ms2":
        return hg < ag
    if key in ("o15", "o25", "o35", "o45"):
        return hg + ag > {"o15": 1.5, "o25": 2.5, "o35": 3.5, "o45": 4.5}[key]
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
         "vb": [0, 0, 0.0], "sur": [0, 0], "rp": {2: [0, 0], 1: [0, 0]}}
    for e in entries:
        rp = e.get("rp")
        if rp and rp.get("t") in (1, 2):
            o = outcome(rp["c"], e["res"])
            if o is not None:
                g["rp"][rp["t"]][1] += 1
                g["rp"][rp["t"]][0] += bool(o)
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


# ------------------------------------------------------------ günün kuponları
COUPON_MIN = 0.55       # güvenli ve bahis türü kuponları: en az bu olasılık
MARKET_MAX = 6          # bahis türü kuponlarında en fazla maç
IY15_MIN = 0.30
IYKG_MIN = 0.15
COUPON_MAX = 8
TARGET_P = (0.55, 0.85) # oran hedefli kuponda kullanılacak tahmin aralığı (adil oran ~1.18-1.82)
TARGETS = (2.0, 5.0)
LOW_VALUE = {"o1.5", "u3.5", "iy05"}   # oranı genelde 1.20 altı kalan tahminler; hedefli kuponda kullanılmaz

# (anahtar, başlık, açıklama, karnedeki kısa ad)
COUPONS = [
    ("guvenli", "Güvenli kupon",
     f"Her maç için modelin en yüksek olasılık verdiği tahmin (%{COUPON_MIN * 100:.0f} ve üzeri). "
     "Oranları düşüktür; tek tek tutma ihtimali yüksek ama hepsi birden zor tutar.", "Güvenli"),
    ("hedef2", "Oran hedefli kupon (~2.00)",
     "Toplam oranı yaklaşık 2.00'ye ulaşana kadar en yüksek ihtimalli maçlar eklenir. 1.5 Üst / 3.5 Alt gibi "
     "1.20 altı tahminler kullanılmaz.", "~2.00"),
    ("hedef5", "Oran hedefli kupon (~5.00)",
     "Aynı mantıkla toplam oranı yaklaşık 5.00'ye ulaşan kupon.", "~5.00"),
    ("o25", "En güvenli 2.5 Üst", "2.5 Üst ihtimali en yüksek maçlar.", "2.5Ü"),
    ("o35", "En güvenli 3.5 Üst", "3.5 Üst ihtimali en yüksek maçlar (genelde %55'in altında kalır).", "3.5Ü"),
    ("kg", "En güvenli KG Var", "İki takımın da gol atma ihtimali en yüksek maçlar.", "KG"),
    ("ms", "En güvenli taraf (MS 1 / MS 2)", "Kazanan tarafın en net göründüğü maçlar.", "MS"),
    ("surpriz", "Sürpriz kuponu: İY/MS 2/1 - 1/2",
     "Sürpriz radarındaki maçlar. Tek tek bile düşük ihtimalli, yüksek oranlı tahminlerdir.", "2/1-1/2"),
    ("iy15", "İY 1.5 Üst kuponu", "İlk yarıda en az 2 gol ihtimali en yüksek maçlar.", "İY1.5Ü"),
    ("iykg", "İY KG Var kuponu", "İlk yarıda iki takımın da gol atma ihtimali en yüksek maçlar.", "İYKG"),
]


def leg_options(r):
    o = [("MS 1", "1", r["p1"]), ("MS X", "X", r["px"]), ("MS 2", "2", r["p2"]),
         ("Çifte şans 1X", "1X", r["p1"] + r["px"]), ("Çifte şans X2", "X2", r["px"] + r["p2"]),
         ("Çifte şans 12", "12", r["p1"] + r["p2"]),
         ("1.5 Üst", "o1.5", r["o15"]), ("2.5 Üst", "o2.5", r["o25"]), ("2.5 Alt", "u2.5", 1 - r["o25"]),
         ("3.5 Üst", "o3.5", r["o35"]), ("3.5 Alt", "u3.5", 1 - r["o35"]),
         ("KG Var", "kg", r["btts"]), ("KG Yok", "kgy", 1 - r["btts"])]
    if r.get("iy05") is not None:
        o.append(("İY 0.5 Üst", "iy05", r["iy05"]))
    return o


def settle_leg(code, res):
    """Kupon bacağı tuttu mu? Sonuç yoksa ya da İY skoru bilinmiyorsa None."""
    if not res:
        return None
    hg, ag, h1, a1 = res
    if code in ("1", "X", "2"):
        return res3(hg, ag) == {"1": 0, "X": 1, "2": 2}[code]
    if code == "1X":
        return hg >= ag
    if code == "X2":
        return hg <= ag
    if code == "12":
        return hg != ag
    if code == "kg":
        return hg > 0 and ag > 0
    if code == "kgy":
        return not (hg > 0 and ag > 0)
    if code[0] in "ou" and code[1:2].isdigit():
        return settle(code, hg, ag)
    if h1 is None:
        return None
    if code == "iy05":
        return h1 + a1 >= 1
    if code == "iy15":
        return h1 + a1 >= 2
    if code == "iykg":
        return h1 > 0 and a1 > 0
    if code == "21":
        return h1 < a1 and hg > ag
    if code == "12r":
        return h1 > a1 and hg < ag
    return None


def build_coupons(leagues, now, only=None):
    cards = [(L, c) for L in leagues for c in L["cards"] if c["state"] == "pre" and c["kick"] > now]

    def leg(L, c, label, code, p, odd=None):
        x = {"id": c["id"], "k": c["kick"].isoformat(), "lg": L["name"], "h": c["home"], "a": c["away"],
             "l": label, "c": code, "p": round(p, 4)}
        if odd:
            x["o"] = odd
        return x

    def top(key, label, code, minp, n=MARKET_MAX):
        legs = [leg(L, c, label, code, c["r"][key]) for L, c in cards
                if c["r"].get(key) is not None and c["r"][key] >= minp]
        return sorted(legs, key=lambda x: -x["p"])[:n]

    out = {"t": now.isoformat()}
    want = lambda k: only is None or k in only  # noqa

    if want("guvenli"):
        safe = []
        for L, c in cards:
            opts = [x for x in leg_options(c["r"]) if x[2] >= COUPON_MIN]
            if opts:
                safe.append(leg(L, c, *max(opts, key=lambda x: x[2])))
        out["guvenli"] = sorted(safe, key=lambda x: -x["p"])
    for tgt, key in zip(TARGETS, ("hedef2", "hedef5")):
        if not want(key):
            continue
        cand = []
        for L, c in cards:
            opts = [x for x in leg_options(c["r"]) if TARGET_P[0] <= x[2] <= TARGET_P[1]
                    and x[1] not in LOW_VALUE]
            if opts:
                cand.append(leg(L, c, *max(opts, key=lambda x: x[2])))
        legs, odds = [], 1.0
        for x in sorted(cand, key=lambda x: -x["p"]):
            if odds >= tgt or len(legs) >= COUPON_MAX:
                break
            legs.append(x)
            odds /= x["p"]
        out[key] = legs if odds >= tgt * 0.9 else []
    if want("o25"):
        out["o25"] = top("o25", "2.5 Üst", "o2.5", COUPON_MIN)
    if want("o35"):
        out["o35"] = top("o35", "3.5 Üst", "o3.5", 0.35)
    if want("kg"):
        out["kg"] = top("btts", "KG Var", "kg", COUPON_MIN)
    if want("ms"):
        ms = []
        for L, c in cards:
            r = c["r"]
            lab, code, p = ("MS 1", "1", r["p1"]) if r["p1"] >= r["p2"] else ("MS 2", "2", r["p2"])
            if p >= COUPON_MIN:
                ms.append(leg(L, c, lab, code, p))
        out["ms"] = sorted(ms, key=lambda x: -x["p"])[:MARKET_MAX]
    if want("surpriz"):
        sur = []
        for L, c in cards:
            if c["surprise"]:
                x = max(c["surprise"], key=lambda s: s["score"])
                sur.append(leg(L, c, "İY/MS " + x["t"], "21" if x["t"] == "2/1" else "12r", x["p"]))
        out["surpriz"] = sorted(sur, key=lambda x: -x["p"])
    if want("iy15"):
        out["iy15"] = top("iy15", "İY 1.5 Üst", "iy15", IY15_MIN, COUPON_MAX)
    if want("iykg"):
        out["iykg"] = top("iykg", "İY KG Var", "iykg", IYKG_MIN, COUPON_MAX)
    if want("deger"):
        dv = []
        for L, c in cards:
            if c["vb"]:
                v = c["vb"][0]
                dv.append(leg(L, c, v["lab"], {"o1.5": "o1.5", "o2.5": "o2.5", "o3.5": "o3.5"}.get(v["code"], v["code"]),
                              v["p"], v["o"]))
        out["deger"] = sorted(dv, key=lambda x: -x["p"])
    return out


def update_coupons(st, leagues, now):
    """Günün kuponu, günün ilk çalıştırmasında bir kez kurulur; sonraki çalıştırmalar sonuçları işler.
    Sonradan eklenen kupon türleri eksikse, başlamamış maçlardan tamamlanır."""
    d0, _ = day_window(now)
    day = f"{d0:%Y-%m-%d}"
    kup = st.setdefault("kupon", {})
    if day not in kup:
        kup[day] = build_coupons(leagues, now)
    else:
        missing = {k for k, *_ in COUPONS if k not in kup[day]}
        if missing:
            kup[day].update({k: v for k, v in build_coupons(leagues, now, missing).items() if k in missing})
    cut = f"{(d0 - dt.timedelta(days=KEEP_DAYS)):%Y-%m-%d}"
    st["kupon"] = {k: v for k, v in kup.items() if k >= cut}
    return st["kupon"][day]


def leg_result(st, results, leg):
    res = results.get(leg["id"]) or (st["preds"].get(leg["id"]) or {}).get("res")
    return settle_leg(leg["c"], res), res


def coupon_grade(st, results, legs):
    won = lost = 0
    for lg in legs:
        ok, _ = leg_result(st, results, lg)
        if ok is True:
            won += 1
        elif ok is False:
            lost += 1
    return won, lost, len(legs)


def prod_p(legs):
    p = 1.0
    for lg in legs:
        p *= lg["p"]
    return p


def legs_table(st, results, legs, now, order="time"):
    show_odd = any(lg.get("o") for lg in legs)
    out = ("<div class='wrap'><table><tr><th>Saat</th><th>Maç</th><th>Tahmin</th><th class='n'>%</th>"
           f"{'<th class=n>Oran</th>' if show_odd else ''}<th class='n'>Durum</th></tr>")
    key = (lambda x: -x["p"]) if order == "p" else (lambda x: x["k"])
    for lg in sorted(legs, key=key):
        k = dt.datetime.fromisoformat(lg["k"])
        ok, res = leg_result(st, results, lg)
        if ok is True:
            dur = f"<span class='pos'>✓ {res[0]}-{res[1]}</span>"
        elif ok is False:
            dur = f"<span class='neg'>✗ {res[0]}-{res[1]}</span>"
        else:
            dur = "canlı" if k <= now else "–"
        odd = f"<td class='n'>{lg['o']:.2f}</td>" if show_odd else ""
        out += (f"<tr><td>{k.astimezone(TR):%H:%M}</td><td>{E(lg['h'])} - {E(lg['a'])}<br>"
                f"<span class='note'>{E(lg['lg'])}</span></td><td><b>{E(lg['l'])}</b></td>"
                f"<td class='n'>{pct(lg['p'])}</td>{odd}<td class='n'>{dur}</td></tr>")
    return out + "</table></div>"


def coupon_footer(st, results, legs, label=""):
    p = prod_p(legs)
    won, lost, n = coupon_grade(st, results, legs)
    out = (f"<div class='cpf'><span>{label}{n} maç</span><span>Hepsi tutar: <b>%{p * 100:.3g}</b></span>"
           f"<span>Yaklaşık toplam oran: <b>{1 / p:,.2f}</b></span></div>")
    if won or lost:
        out += f"<div class='row'>Şu ana kadar <b class='pos'>{won} tuttu</b> · <b class='neg'>{lost} yattı</b></div>"
    return out


def coupon_html(st, results, key, title, desc, legs, now):
    out = f"<div class='card' id='cp-{key}'><h2>{E(title)}</h2><p class='note'>{E(desc)}</p>"
    if not legs:
        return out + "<p class='empty'>Bugün bu kupona uyan maç yok.</p></div>"
    order = "p" if key in ("guvenli", "o25", "o35", "kg", "ms", "iy15", "iykg") else "time"
    out += legs_table(st, results, legs, now, order) + coupon_footer(st, results, legs)
    if key == "guvenli" and len(legs) > 3:
        best = sorted(legs, key=lambda x: -x["p"])
        for size in (3, 5):
            if len(best) > size:
                sub = best[:size]
                out += (f"<div class='sub'><h3>En güvenli {size}'li</h3>" + legs_table(st, results, sub, now, "p")
                        + coupon_footer(st, results, sub) + "</div>")
    elif key in ("o25", "o35", "kg", "ms", "iy15", "iykg") and len(legs) > 3:
        out += coupon_footer(st, results, sorted(legs, key=lambda x: -x["p"])[:3], "İlk 3'lü: ")
    if prod_p(legs) < 0.05:
        out += ("<p class='warn'>Bu kuponun tamamının tutma ihtimali çok düşük. Maçları tek tek ya da küçük "
                "gruplar halinde değerlendirmek daha gerçekçi.</p>")
    return out + "</div>"


def coupons_tab(st, coupons, results, now):
    chips = "".join(f"<a class='chip' href='#cp-{k}'>{E(short)} <small>{len(coupons.get(k, []))}</small></a>"
                    for k, _, _, short in COUPONS)
    out = ("<h2>Günün kuponları</h2><p class='note'>Kuponlar günün ilk çalıştırmasında (08:00) kurulur ve gün boyu "
           "değişmez; maçlar bittikçe Durum sütunu dolar.</p><div class='chips'>{chips}</div>")
    for key, title, desc, _ in COUPONS:
        out += coupon_html(st, results, key, title, desc, coupons.get(key, []), now)
    return out


def coupon_karne(st, results):
    days = sorted(st.get("kupon", {}), reverse=True)[:14]
    if not days:
        return ""
    head = "".join(f"<th class='n'>{E(short)}</th>" for *_, short in COUPONS)
    out = ("<h3>Kupon karnesi</h3><p class='note'>Her hücre: tutan maç / toplam maç. ✓ kuponun tamamı tuttu, "
           "✗ en az bir maç yattı.</p><div class='wrap'><table><tr><th>Gün</th>" + head + "</tr>")
    for d in days:
        out += f"<tr><td>{d[8:]}.{d[5:7]}</td>"
        for key, *_ in COUPONS:
            legs = st["kupon"][d].get(key, [])
            if not legs:
                out += "<td class='n'>-</td>"
                continue
            won, lost, n = coupon_grade(st, results, legs)
            mark = " <span class='neg'>✗</span>" if lost else (" <span class='pos'>✓</span>" if won == n else "")
            out += f"<td class='n'>{won}/{n}{mark}</td>"
        out += "</tr>"
    return out + "</table></div>"


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
    global PREV_SNAPSHOT
    now = dt.datetime.now(UTC)
    PREV_SNAPSHOT = snapshot_from_html()       # sayfa yeniden yazılmadan önce önceki durumu oku
    load_odds()
    leagues = {}
    # önce yerel ligler: kupa maçlarındaki lig gücü düzeltmesi bunlara dayanır
    for slug, name, cal in sorted(LEAGUES, key=lambda x: x[0].startswith("uefa.")):
        if slug.startswith("uefa.") and not CUP_ALL and not FETCHED:
            for L in leagues.values():
                if not L["err"] and L.get("allm"):
                    CUP_DOM[L["slug"]] = sorted([m for m in L["allm"] if m["done"]], key=lambda m: m["date"])
            for cs, _, _ in LEAGUES:
                if cs.startswith("uefa."):
                    try:
                        FETCHED[cs] = fetch_league(cs, now)
                    except Exception as e:  # noqa
                        print("kupa verisi alınamadı:", cs, e, flush=True)
            cup_ids = set()
            for fin, _ in FETCHED.values():
                for m in fin:
                    if m["id"] not in cup_ids:
                        cup_ids.add(m["id"])
                        m["cup"] = True
                        CUP_ALL.append(m)
            CUP_ALL.sort(key=lambda m: m["date"])
        print("Lig:", slug, flush=True)
        leagues[slug] = process_league(slug, name, cal, now)
    leagues = [leagues[s] for s, _, _ in LEAGUES]
    allraw = [x for L in leagues for x in L.get("raw", [])]
    cut = now - dt.timedelta(days=BACKTEST_DAYS)
    pool_eval = fit_kc([x for x in allraw if x["date"] < cut])
    pool_all = fit_kc(allraw)
    print("ortak ayar:", pool_eval, pool_all, flush=True)
    global TRUST, TRUST_EVAL, GLOBAL_TH
    rp_rows = [(x["rp"], x["date"]) for x in allraw if "rp" in x]
    TRUST_EVAL = trust_from([rp for rp, d in rp_rows if d < cut])   # sadece eski günlerle öğrenilir
    TRUST = trust_from([rp for rp, _ in rp_rows])                   # bugünkü öneriler için tüm geçmiş
    seen, allpast = set(), []
    for L in leagues:
        if "_ctx" in L:
            for m in L["_ctx"][1]:
                if m["id"] not in seen:
                    seen.add(m["id"])
                    allpast.append(m)
    GLOBAL_TH = team_history(sorted(allpast, key=lambda m: m["date"]))
    global LIVE_CTX
    LIVE_CTX = live_context(leagues, allpast)
    for L in leagues:
        finish_league(L, now, pool_eval, pool_all)
    update_odds_archive(leagues, now)
    MACS_BY_ID.update(write_maclar(leagues, now))
    st = load_store()
    update_store(st, leagues, now)
    update_log(st, make_snapshot(leagues, now), PREV_SNAPSHOT, now)
    update_coupons(st, leagues, now)
    write_html(leagues, now, st)
    write_live_model(leagues, now)
    write_live_html()
    write_bet_html()
    write_analiz(leagues, now)
    write_analiz_html()
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
nav{position:sticky;top:0;background:var(--bg);padding:8px 12px;z-index:5}
nav select{width:100%;font-size:16px;font-weight:600;padding:10px 12px;border-radius:10px;background:var(--card);color:var(--tx);border:1px solid var(--bd)}
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
.chips{display:flex;flex-wrap:wrap;gap:6px;margin:8px 0 12px}
.chip{border:1px solid var(--bd);background:var(--card);color:var(--tx);border-radius:14px;padding:5px 10px;font-size:12.5px;text-decoration:none}
.chip small{color:var(--mu)}
.cpf{display:flex;flex-wrap:wrap;gap:4px 14px;font-size:13px;color:var(--mu);margin-top:8px;padding-top:8px;border-top:1px dashed var(--bd)}
.cpf b{color:var(--tx)}
.sub{margin-top:14px;padding:10px;border-radius:10px;background:var(--lo)}
.sub h3{margin:0 0 4px}
html{scroll-behavior:smooth;scroll-padding-top:56px}
.alarm{border:2px solid #d93025;border-radius:12px;padding:10px 12px;margin:8px 0 2px;background:var(--card)}
.ah{display:flex;justify-content:space-between;align-items:center;gap:8px;font-size:14px}
.live{display:inline-block;background:#d93025;color:#fff;font-size:11px;font-weight:700;padding:2px 7px;border-radius:6px;animation:bl 1.6s infinite}
@keyframes bl{50%{opacity:.55}}
.arow{display:block;text-decoration:none;color:var(--tx);border-top:1px solid var(--bd);padding:8px 0 6px;margin-top:6px}
.at{font-size:13.5px}.ab{font-size:14px;margin-top:3px}.ar{font-size:12px;color:var(--warn);margin-top:3px}
.lv{font-size:10.5px;font-weight:800;padding:1px 6px;border-radius:5px;color:#fff;background:var(--warn)}
.arow.kritik .lv{background:#d93025}
"""

JS = """
function show(id){
  document.querySelectorAll('.tab').forEach(function(e){e.classList.toggle('on',e.id===id)});
  var s = document.getElementById('navsel'); if(s && s.value!==id) s.value = id;
  window.scrollTo(0,0);
}
function t1Filter(){
  var v = document.getElementById('t1lg').value;
  document.querySelectorAll('details.t1m').forEach(function(e){ e.style.display = (!v || e.dataset.lg===v) ? '' : 'none'; });
}
"""

E = html.escape


def box(label, p, odd=None, val=False):
    extra = ""
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
            f"<th class='n'>Model</th><th class='n'>Benzer {sst['n']} maçta</th></tr>")
    for s_ in shown:
        p = r["scores"].get(s_, 0)
        k = sst["scores"].get(s_, 0)
        out += (f"<tr{' class=hl' if s_ == shown[0] else ''}><td>{s_}</td><td class='n'>{pct(p)}</td>"
                f"<td class='n'>{k} kez ({pct(k / sst['n']) if sst['n'] else '-'})</td></tr>")
    out += "</table></div>"
    if r.get("p21") is not None:
        out += (f"<div class='row'>İY/MS sürpriz: 2/1 <b>{pct(r['p21'])}</b> (benzer maçlarda "
                f"{sst['r21']}/{sst['nht']}) · 1/2 <b>{pct(r['p12'])}</b> (benzer maçlarda "
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
            "<th class='n'>Benzer</th></tr>")
    for x, c in items[:6]:
        out += (f"<tr><td>{c['time']} {E(c['home'])} - {E(c['away'])}<br><span class='note'>{E(c['league'])}</span></td>"
                f"<td><b>{x['t']}</b></td><td class='n'>{pct(x['p'])}</td>"
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
            "getiri = model olasılığı × oran − 1. Sadece modelin o ligde o bahis türünde geçmiş "
            "testte lig ortalamasını geçtiği durumlar gösterilir.</p><div class='wrap'><table><tr><th>Maç</th><th>Bahis</th>"
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
    out = "<h2>Günün özeti</h2>" + radar_html(leagues)
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
    out += "<tr><td><b>Rapor: Güçlü öneri</b></td>" + "".join(f"<td class='n'>{ratio(*g['rp'][2])}</td>" for _, g in per) + "</tr>"
    out += "<tr><td><b>Rapor: Orta öneri</b></td>" + "".join(f"<td class='n'>{ratio(*g['rp'][1])}</td>" for _, g in per) + "</tr>"
    out += "<tr><td>Sürpriz radarı</td>" + "".join(f"<td class='n'>{ratio(*g['sur'])}</td>" for _, g in per) + "</tr>"
    out += "</table></div>"

    return out


def karne_tab(st, now):
    per = periods(st, now)
    out = ("<h2>Karne</h2><p class='note'>Bot her sabah başlamamış maçların tahminini kaydeder, maç "
           "bitince sonucu işler. Burada sadece maç başlamadan yapılmış tahminler sayılır. Üst/Alt ve "
           f"KG satırlarında model %{CONF * 100:.0f} ve üstü (ya da %{(1 - CONF) * 100:.0f} ve altı) "
           "dediği maçlar sayılır.</p>")
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
                "<th class='n'>Güçlü öneri</th><th class='n'>2.5 Ü/A</th><th class='n'>KG</th></tr>")
        for d in days:
            g = grade([e for e in st["preds"].values() if e["d"] == d and e.get("res")])
            h25, t25 = g["mk"]["2.5 Üst/Alt"]
            hk, tk = g["mk"]["KG Var/Yok"]
            c25 = f"{h25}/{t25}" if t25 else "-"
            ckg = f"{hk}/{tk}" if tk else "-"
            hs, ts = g["rp"][2]
            cg = f"{hs}/{ts}" if ts else "-"
            out += (f"<tr><td>{d[8:]}.{d[5:7]}</td><td class='n'>{g['n']}</td><td class='n'><b>{cg}</b></td>"
                    f"<td class='n'>{c25}</td><td class='n'>{ckg}</td></tr>")
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


def xw_cells(L):
    r = L.get("xwres") or {}
    if not r:
        return f"<td class='n'>-</td><td class='n'>{'veri yok' if L.get('xcov', 0) < 0.5 else '-'}</td>"
    w = L.get("xw", 0.0)
    b0, bw = r.get(0.0, (0, 0))[1], r.get(w, (0, 0))[1]
    imp = (b0 - bw) / b0 * 100 if b0 else 0
    cls_ = "pos" if imp > 0.05 else ""
    return f"<td class='n'>{w:.2f}</td><td class='n {cls_}'>{'-%.1f%%' % imp if imp > 0.05 else '0'}</td>"


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
            "yüzdeler ortalamaya çekildi. Ayar c: 1'den büyükse model golü az tahmin ediyordu ve artırıldı. "
            "Şut ağırlığı: takım gücü hesabında şut kalitesinin gole göre payı (0 = sadece gol); bot bunu her gün "
            "geçmiş 150 günde en iyi tahmini veren değere göre seçer. 2.5Ü hata: bu seçimin 2.5 Üst tahmin "
            "hatasını sadece gole göre ne kadar azalttığı.</p>")
    out += ("<div class='wrap'><table><tr><th>Lig</th><th class='n'>Ev avantajı</th>"
            "<th class='n'>İY payı</th><th class='n'>DC ρ</th><th class='n'>İY veri</th>"
            "<th class='n'>Ayar k</th><th class='n'>Ayar c</th><th class='n'>Şut ağırlığı</th>"
            "<th class='n'>2.5Ü hata</th></tr>")
    for L in leagues:
        m = L.get("model")
        if not m:
            continue
        hm = m.get("half")
        out += (f"<tr><td>{E(L['name'])}</td><td class='n'>{m['ha'] ** 2:.2f}</td>"
                f"<td class='n'>{pct(hm['f']) if hm else '-'}</td><td class='n'>{m['rho']:+.2f}</td>"
                f"<td class='n'>{pct(hm['cov']) if hm else '-'}</td>"
                f"<td class='n'>{L['kc'][0]:.2f}{'*' if L.get('kc_src') == 'ortak' else ''}</td>"
                f"<td class='n'>{L['kc'][1]:.2f}</td>{xw_cells(L)}</tr>")
    out += ("</table></div><p class='note'>* Bu ligin yeterli geçmiş testi olmadığı için tüm liglerin "
            "ortak ayarı kullanıldı.</p>")
    return out


# ------------------------------------------------------------ gol raporu sekmesi
RP_CSS = """
.rpchips{display:flex;flex-wrap:wrap;gap:6px;padding:4px 0 10px}
.rpchips button{border:1px solid var(--bd);background:var(--card);color:var(--tx);border-radius:14px;padding:6px 11px;font-size:12.5px;flex:none}
.rpchips button.on{background:var(--tx);color:var(--bg);border-color:var(--tx)}
.rps{display:none}.rps.on{display:block}
details.rp{background:var(--card);border-radius:12px;margin-bottom:8px;padding:10px 12px}
details.rp summary{list-style:none;cursor:pointer;margin:0}
details.rp summary::-webkit-details-marker{display:none}
.rt{display:flex;justify-content:space-between;align-items:center;font-size:12px;color:var(--mu)}
.rm{font-size:15px;margin-top:3px}.rb{font-size:14px;margin-top:3px}
.tier{font-size:10.5px;font-weight:800;padding:2px 7px;border-radius:5px;color:#fff}
.tier.t2{background:#0a7d3b}.tier.t1{background:#b26a00}.tier.t0{background:#777}
ul.ck{list-style:none;padding:0;margin:10px 0 6px}
ul.ck li{font-size:13px;padding:4px 0;border-bottom:1px solid var(--bd)}
ul.ck li.y::before{content:'✓ ';color:var(--ac);font-weight:800}
ul.ck li.n::before{content:'✗ ';color:var(--neg);font-weight:800}
ul.ck li.n{color:var(--mu)}
ul.ck li.i::before{content:'ℹ ';color:var(--mu)}
.tc{font-size:12.5px;margin:6px 0;line-height:1.5}
.fm b{display:inline-block;width:15px;text-align:center;border-radius:3px;color:#fff;font-size:10.5px;margin-right:1px}
.fm .G{background:#0a7d3b}.fm .B{background:#888}.fm .M{background:#c0392b}
.yorum{font-size:13px;line-height:1.5;background:var(--lo);border-radius:8px;padding:8px 10px;margin:8px 0}
.res{font-size:12px;font-weight:700;margin-left:6px}
.no{display:inline-block;width:17px;height:17px;line-height:17px;text-align:center;border-radius:50%;background:var(--tx);color:var(--bg);font-size:11px;font-weight:800;margin-right:6px}
.r2{color:var(--mu);font-size:13px}.r2 .no{background:var(--mu)}
.hist{font-size:12.5px;margin:4px 0 2px;color:var(--mu)}
.bt td.up{color:var(--ac);font-weight:700}.bt td.dn{color:var(--neg);font-weight:700}
.tf{display:flex;align-items:center;gap:6px;flex-wrap:wrap;font-size:13px;margin:10px 0 2px}
.tf select{background:var(--card);color:var(--tx);border:1px solid var(--bd);border-radius:8px;padding:6px 4px;font-size:13px}
.tf button{border:1px solid var(--bd);background:var(--card);color:var(--tx);border-radius:14px;padding:6px 10px;font-size:12.5px}
"""

RP_JS = """
function rpStarted(e, now){ return e.dataset.d==='1' || now >= parseInt(e.dataset.k); }
function rpFilter(){
  var tf = document.querySelector('.tf'); if(!tf) return;
  var s = parseInt(tf.dataset.s), now = Date.now();
  var a = s + parseInt(document.getElementById('tf-a').value)*3600e3;
  var b = s + parseInt(document.getElementById('tf-b').value)*3600e3;
  document.querySelectorAll('.rps').forEach(function(sec){
    var n = 0, fin = sec.id==='rps-done';
    sec.querySelectorAll('details.rp').forEach(function(e){
      var k = parseInt(e.dataset.k), st = rpStarted(e, now);
      var show = fin ? st : (!st && k>=a && k<b);
      e.style.display = show ? '' : 'none'; if(show) n++;
    });
    var c = sec.querySelector('.cnt'); if(c) c.textContent = n+' maç';
    var z = sec.querySelector('.none'); if(z) z.style.display = n ? 'none' : '';
  });
}
function tfAll(){ document.getElementById('tf-a').value='0'; document.getElementById('tf-b').value='24'; rpFilter(); }
function tfNext(h){
  var s = parseInt(document.querySelector('.tf').dataset.s);
  var a = Math.max(0, Math.floor((Date.now()-s)/3600e3)), b = Math.min(24, a+h);
  document.getElementById('tf-a').value = String(Math.min(a,23)); document.getElementById('tf-b').value = String(Math.max(b,1)); rpFilter();
}
document.addEventListener('DOMContentLoaded', rpFilter);
setInterval(rpFilter, 60000);
function rpShow(k){
  document.querySelectorAll('.rps').forEach(function(e){e.classList.toggle('on', e.id==='rps-'+k)});
  document.querySelectorAll('.rpchips button').forEach(function(e){e.classList.toggle('on', e.dataset.k===k)});
}
"""


def rp_outcome(c, key):
    if not c["score"]:
        return None
    ht = c.get("ht")
    return gev(key, c["score"][0], c["score"][1], ht[0] if ht else None, ht[1] if ht else None)


def form_html(form):
    return "<span class='fm'>" + "".join(f"<b class='{x}'>{x}</b>" for x in form) + "</span>"


def team_line(name, t):
    pos = f"{t['rank']}. sıra · {t['pts']} puan ({t['pl']} maç) · {t['tag']}" if t["rank"] else "sıralama yok"
    goals = (f"Son 10: maç başı {num(t['gf'])} attı, {num(t['ga'])} yedi"
             + (f" (ilk yarı {num(t['gf1'])} / {num(t['ga1'])})" if t["gf1"] is not None else ""))
    last = " · ".join(f"{'G' if gf > ga else ('B' if gf == ga else 'M')} {gf}-{ga} {E(opp)}{'' if home else ' (d)'}"
                      for opp, gf, ga, home in t["last5"])
    extra = ""
    if t.get("sf") is not None:
        extra += (f"<br>Şut: maç başı {t['sf']:.1f} isabetli (rakibe {t['sa']:.1f})"
                  + (f" · korner {t['cf']:.1f}" if t.get("cf") is not None else "")
                  + (f" · şutlara göre beklenen gol {t['xf']:.1f} / yenen {t['xa']:.1f}" if t.get("xf") is not None else ""))
    if t.get("luck") is not None and abs(t["luck"]) >= 3:
        extra += (f"<br><span class='warn'>Son 10 maçta şutlarına göre {t['luck']:+.0f} gol "
                  + ("fazla attı: şanslı gidiyor, gol ortalaması düşebilir" if t["luck"] > 0
                     else "az attı: şanssız gidiyor, gol ortalaması artabilir") + "</span>")
    if t.get("rest") is not None and t["rest"] <= 10:
        extra += (f"<br>Son maçından bu yana {t['rest']} gün"
                  + (" · <span class='warn'>yorgunluk / rotasyon riski</span>" if t["rest"] <= 3 else ""))
    return (f"<div class='tc'><b>{E(name)}</b> · {pos}<br>Form (yeniden eskiye): {form_html(t['form'])} · {goals}"
            f"{extra}<br><span class='note'>Son 5: {last}</span></div>")


def hist_text(key, tier):
    t = (TRUST or {}).get((key, tier))
    if not t or tier not in (1, 2):
        return ""
    good = t["hit"] >= t["base"] + TRUST_LIFT and t["n"] >= TRUST_MIN_N
    col = "pos" if good else "neg"
    return (f"<div class='hist'>Geçmiş: {TIER_NAME[tier].capitalize()} {GM_LABEL[key]} önerileri "
            f"<b class='{col}'>%{t['hit'] * 100:.0f}</b> tuttu ({t['n']} maç; tüm maçlarda %{t['base'] * 100:.0f})</div>")


def rp_comment(c, key, context=True):
    h, a = c["tctx"]["h"], c["tctx"]["a"]
    ev = c["rapor"]["m"][key]
    out = []
    lam, lam1 = c["lam"], c["r"].get("lam1")
    if not context:
        h = dict(h, rank=None, gf=None)
    xg = f"Model maçta toplam {lam[0] + lam[1]:.1f} gol bekliyor ({c['home']} {lam[0]:.1f}, {c['away']} {lam[1]:.1f})"
    if lam1:
        xg += f"; ilk yarıda {lam1[0] + lam1[1]:.1f}"
    if context:
        out.append(xg + ".")
    if h["rank"] and a["rank"]:
        out.append(f"{c['home']} ligde {h['rank']}. sırada ({h['tag']}), {c['away']} {a['rank']}. sırada ({a['tag']}).")
        if h["pl"] >= 4 and a["pl"] >= 4 and abs(h["rank"] - a["rank"]) >= max(6, h["n"] // 3):
            fav = c["home"] if h["rank"] < a["rank"] else c["away"]
            out.append(f"Sıralamada belirgin fark var; {fav} kâğıt üstünde güçlü taraf.")
    if h["gf"] is not None and a["gf"] is not None and c.get("lavg"):
        hm, am = h["gf"] + h["ga"], a["gf"] + a["ga"]
        out.append(f"{c['home']} maçlarında son 10'da ortalama {hm:.1f}, {c['away']} maçlarında {am:.1f} gol çıktı "
                   f"(lig ortalaması {c['lavg']:.1f}).")
    goods = [t for ok, t in ev["checks"] if ok]
    fails = [t for ok, t in ev["checks"] if not ok]
    out.append(f"{GM_LABEL[key]} için {ev['ok']}/{ev['tot']} kriter tutuyor.")
    if len(goods) > 1:
        out.append("En güçlü dayanak: " + goods[1] + ".")
    if fails:
        out.append("Aleyhine: " + "; ".join(fails[:2]) + ".")
    return " ".join(out)


def bet_block(c, key, title="", context=True):
    ev = c["rapor"]["m"][key]
    checks = "".join(f"<li class='{'y' if ok else 'n'}'>{E(t)}</li>" for ok, t in ev["checks"])
    checks += "".join(f"<li class='i'>{E(t)} <span class='note'>· bilgi, {'lehine' if ok else 'aleyhine'}</span></li>"
                      for ok, t in ev.get("info", []))
    head = (f"<div class='sec'>{title}{GM_LABEL[key]} · {ev['ok']}/{ev['tot']} kriter · model %{ev['p'] * 100:.0f} "
            f"<span class='tier t{ev['tier']}'>{TIER_NAME[ev['tier']]}</span></div>") if title else ""
    return (f"{head}<ul class='ck'>{checks}</ul>{hist_text(key, ev['tier'])}"
            f"<div class='yorum'>{E(rp_comment(c, key, context))}</div>")


def gi_html(c):
    g = c.get("gi") or {}
    h, a, lg = g.get("h"), g.get("a"), g.get("lg")
    if not h or not a or h["n"] < 5 or a["n"] < 5:
        return ""

    def cell(v, n, ref):
        r = v / n
        cls = " class='n pos'" if ref and r >= ref * 1.4 and v >= 3 else " class='n'"
        return f"<td{cls}>{v}</td>"
    rows = ""
    for i, lab in enumerate(GI_LABEL):
        ref = (lg["f"][i] + lg["a"][i]) / 2 if lg else None
        lgc = f"<td class='n'>{(lg['f'][i] + lg['a'][i]):.2f}</td>" if lg else ""
        rows += (f"<tr><td>{lab}</td>{cell(h['f'][i], h['n'], ref)}{cell(h['a'][i], h['n'], ref)}"
                 f"{cell(a['f'][i], a['n'], ref)}{cell(a['a'][i], a['n'], ref)}{lgc}</tr>")
    lgh = "<th class='n'>Lig</th>" if lg else ""

    def frac(t):
        return f"{t[0]}/{t[1]}" if t[1] else "-"

    def line(nm, x):
        return (f"<li><b>{E(nm)}</b> ({x['n']} maç): ilk 30 dk'da gol olan maç {frac(x['early'])} · son 15 dk'da gol olan maç "
                f"{frac(x['late'])} · öne geçince kazandı {frac(x['sfwin'])} · geriye düşünce gol attı {frac(x['reply'])}, "
                f"puan aldı {frac(x['comeback'])} · ilk golden sonra 2+ gol daha {frac(x['open'])}</li>")
    lgl = ""
    if lg:
        lgl = (f"<li><b>Lig ortalaması</b>: ilk 30 dk'da gol %{lg['early'] * 100:.0f} · son 15 dk'da gol %{lg['late'] * 100:.0f} · "
               f"öne geçen kazanır %{lg['sfwin'] * 100:.0f} · geriye düşen gol atar %{lg['reply'] * 100:.0f}, puan alır "
               f"%{lg['comeback'] * 100:.0f} · ilk golden sonra 2+ gol %{lg['open'] * 100:.0f}</li>")
    return ("<div class='sec'>Gol dakikaları ve maç içi tepki</div>"
            f"<p class='note'>Takımların gol dakikası bilinen son maçları. Sayılar gol adedi; yeşil: lig ortalamasının belirgin üstü. "
            f"Lig sütunu: maç başı gol.</p><div class='wrap'><table><tr><th>Dakika</th><th class='n'>{E(c['home'])} attı</th>"
            f"<th class='n'>yedi</th><th class='n'>{E(c['away'])} attı</th><th class='n'>yedi</th>{lgh}</tr>{rows}</table></div>"
            f"<ul class='ck'>{line(c['home'], h)}{line(c['away'], a)}{lgl}</ul>")


def rp_item(c, key, lname, full=True):
    ev = c["rapor"]["m"][key]
    tier = ev["tier"]
    o = rp_outcome(c, key)
    res = ""
    if c["score"]:
        mark = "" if o is None else ("<span class='pos'>✓</span>" if o else "<span class='neg'>✗</span>")
        res = f"<span class='res'>{c['score'][0]}-{c['score'][1]} {mark}</span>"
    elif c["state"] == "in":
        res = "<span class='res' style='color:#d93025'>CANLI</span>"
    kms = int(c["kick"].timestamp() * 1000)
    done = 1 if c["score"] or c["state"] != "pre" else 0
    head = (f"<details class='rp' data-k='{kms}' data-d='{done}'><summary>"
            f"<div class='rt'><span>{c['day']} {c['time']} · {E(lname)}</span><span class='tier t{tier}'>{TIER_NAME[tier]}</span></div>"
            f"<div class='rm'><b>{E(c['home'])} - {E(c['away'])}</b>{res}</div>")
    alt = c["rapor"].get("alt") if full and key == c["rapor"].get("main") else None
    if not full:
        return (head + f"<div class='rb'><b>{GM_LABEL[key]}</b> · {ev['ok']}/{ev['tot']} kriter · model %{ev['p'] * 100:.0f}</div>"
                f"</summary>{bet_block(c, key)}</details>")
    line1 = f"<div class='rb'><span class='no'>1</span><b>{GM_LABEL[key]}</b> · {ev['ok']}/{ev['tot']} kriter · model %{ev['p'] * 100:.0f}</div>"
    line2 = ""
    if alt:
        ea = c["rapor"]["m"][alt]
        line2 = (f"<div class='rb r2'><span class='no'>2</span>{GM_LABEL[alt]} · {ea['ok']}/{ea['tot']} kriter · "
                 f"model %{ea['p'] * 100:.0f} <span class='tier t{ea['tier']}'>{TIER_NAME[ea['tier']]}</span></div>")
    others = "".join(
        f"<tr><td>{GM_LABEL[k]}</td><td class='n'>%{v['p'] * 100:.0f}</td><td class='n'>{v['ok']}/{v['tot']}</td>"
        f"<td class='n'><span class='tier t{v['tier']}'>{TIER_NAME[v['tier']]}</span></td></tr>"
        for k, v in sorted(c["rapor"]["m"].items(), key=lambda kv: (-kv[1]["tier"], -kv[1]["score"])))
    body = bet_block(c, key, "1. öneri: ")
    if alt:
        body += bet_block(c, alt, "2. öneri: ", context=False)
    return (head + line1 + line2 + "</summary>" + body +
            f"{team_line(c['home'], c['tctx']['h'])}{team_line(c['away'], c['tctx']['a'])}{gi_html(c)}"
            "<div class='sec'>Bu maçtaki tüm bahisler</div><div class='wrap'><table><tr><th>Bahis</th>"
            f"<th class='n'>Model</th><th class='n'>Kriter</th><th class='n'>Seviye</th></tr>{others}</table></div></details>")


LEARN_HTML = (
    "<details class='rp'><summary><b>Model kendini nasıl güncelliyor?</b> <span class='note'>(dokun)</span></summary>"
    "<div class='tc'>Bot her çalıştığında (08:00 ve 14:00) en son biten maçlar dahil son ~14 ayın tüm sonuçlarını "
    "yeniden çeker ve şunları baştan hesaplar:<br>1. <b>Takım güçleri</b>: son maçlar daha ağır basar (100 günde ağırlık "
    "yarıya iner, takımın son 10 maçı ekstra önemlidir). Dün 5-1 biten bir maç bugünkü tahminlere zaten girmiştir.<br>"
    "2. <b>Yüzde ayarı</b>: modelin geçmişte fazla/az gol tahmin edip etmediği ölçülüp düzeltilir.<br>"
    "2b. <b>Şut verisi</b>: goller şansa açık olduğu için takım gücü isabetli/isabetsiz şutlardan hesaplanan "
    "'şut kalitesi' ile karıştırılır. Ne kadar karıştırılacağını bot her gün geçmiş 150 günde en iyi tahmini "
    "veren orana göre seçer (Doğruluk sekmesi, 'Şut ağırlığı').<br>"
    "3. <b>Kontrol listesi eşikleri</b>: ligin güncel gol, KG ve ilk yarı oranları her gün yeniden hesaplanır.<br>"
    "4. <b>Güven filtresi (öğrenme)</b>: son 150 günde her bahis türünün Güçlü/Orta önerileri gerçekte ne kadar "
    "tuttuğu ölçülür. Ortalamadan en az 3 puan iyi değilse o bahis türü <b>günün önerisi olarak seçilmez</b>. "
    "Böylece hangi bahisler tutmaya başlarsa sistem onlara kayar, tutmayanları kendiliğinden bırakır.<br>"
    "Sınırı: Model kadro, sakatlık, motivasyon gibi sonuçlara yansımamış bilgileri bilemez.</div></details>")


def gated_headline(leagues):
    if not TRUST_EVAL:
        return ""
    cut = None
    rows = [(rp, d) for L in leagues for rp, _, d in L.get("rp_bt", [])]
    if not rows:
        return ""
    dmax = max(d for _, d in rows)
    cut = dmax - dt.timedelta(days=BACKTEST_DAYS)
    rec = [rp for rp, d in rows if d >= cut]
    tot = trust_from(rec)
    res = {1: [0, 0], 2: [0, 0]}
    exp = {1: 0.0, 2: 0.0}
    for rp in rec:
        k = pick_main(rp, TRUST_EVAL)
        if k and rp[k][1] is not None:
            t = rp[k][0]
            res[t][0] += rp[k][1]
            res[t][1] += 1
            base = [v for (kk, _), v in tot.items() if kk == k]
            exp[t] += base[0]["base"] if base else 0
    lines = []
    for t in (2, 1):
        h, n = res[t]
        if n:
            lines.append(f"<b>{TIER_NAME[t].capitalize()}</b>: {n} maçta <b>%{h / n * 100:.0f}</b> tuttu "
                         f"(aynı bahisler rastgele maçlarda %{exp[t] / n * 100:.0f})")
    if not lines:
        return ""
    return ("<div class='yorum'><b>Gerçekçi test (öğrenme dahil):</b> Güven filtresi sadece son "
            f"{BACKTEST_DAYS} günden önceki maçlarla öğrendi, sonra son {BACKTEST_DAYS} günde günün önerilerini seçti. "
            + " · ".join(lines) + "</div>")


def rapor_bt(leagues):
    rows = [(rp, mk) for L in leagues for rp, mk, _ in L.get("rp_bt", [])]
    per = {}
    for key, _ in RP_MARKETS:
        allv = [rp[key][1] for rp, _ in rows if key in rp and rp[key][1] is not None]
        t1 = [rp[key][1] for rp, _ in rows if key in rp and rp[key][0] == 1 and rp[key][1] is not None]
        t2 = [rp[key][1] for rp, _ in rows if key in rp and rp[key][0] == 2 and rp[key][1] is not None]
        per[key] = (allv, t1, t2)
    base = {k: (sum(v[0]) / len(v[0]) if v[0] else None) for k, v in per.items()}
    main = {1: [], 2: []}
    for rp, mk in rows:
        if mk and rp.get(mk) and rp[mk][1] is not None:
            main[rp[mk][0]].append((rp[mk][1], base.get(mk)))
    return per, main, len(rows)


def rapor_bt_html(leagues):
    per, main, n = rapor_bt(leagues)
    if not n:
        return ""

    def cell(v, base=None):
        if not v:
            return "<td class='n'>-</td>"
        r = sum(v) / len(v)
        cls_ = ""
        if base is not None and len(v) >= 15:
            cls_ = " up" if r >= base + 0.05 else (" dn" if r <= base - 0.02 else "")
        return f"<td class='n{cls_}'>%{r * 100:.0f} <span class='note'>({len(v)})</span></td>"
    out = (f"<h3>Bu kurallar geçmişte ne kadar tuttu?</h3><p class='note'>Son {BACKTEST_DAYS + CALIB_DAYS} günün "
           f"{n} maçında, her maç yalnızca o güne kadarki verilerle değerlendirildi. Parantez içi maç sayısı. "
           "Yeşil: tüm maçların ortalamasından belirgin iyi; kırmızı: ortalamadan kötü.</p>")
    lines = []
    for t in (2, 1):
        v = main[t]
        if v:
            hit = sum(1 for o, _ in v if o) / len(v)
            exp = sum(b for _, b in v if b is not None) / len(v)
            lines.append(f"<b>{TIER_NAME[t].capitalize()} öneriler</b> {len(v)} maçta <b>%{hit * 100:.0f}</b> tuttu; "
                         f"aynı bahisler rastgele maçlarda ortalama %{exp * 100:.0f} tutardı.")
    if lines:
        out += "<div class='yorum'>" + "<br>".join(lines) + "</div>"
    out += ("<div class='wrap'><table class='bt'><tr><th>Bahis</th><th class='n'>Tüm maçlar</th>"
            "<th class='n'>Orta</th><th class='n'>Güçlü</th></tr>")
    for key, label in RP_MARKETS:
        allv, t1, t2 = per[key]
        b = sum(allv) / len(allv) if allv else None
        out += f"<tr><td>{label}</td>{cell(allv)}{cell(t1, b)}{cell(t2, b)}</tr>"
    return out + "</table></div>"


def rapor_tab(leagues, now):
    cards = [(c, L["name"]) for L in leagues for c in L["cards"] if c.get("rapor")]
    d0, _ = day_window(now)
    out = ("<h2>Gol raporu</h2><p class='note'>Her maçta 8 gol bahsi ve MS 1 / MS 2 için 8 maddelik kontrol "
           "listesi: model, iki takımın son 10 maçı, ev sahibinin evdeki ve deplasmanın dışarıdaki son 5 maçı, benzer "
           "maçlar, aralarındaki maçlar ve gol ortalamaları (MS için puan ortalaması). Bir madde, ligin genel oranının belirgin üstündeyse ✓ alır. "
           "<b>Güçlü</b>: maddelerin en az %80'i ✓. <b>Orta</b>: en az %60'ı. Bir maça dokununca detayı açılır.</p>")
    out += gated_headline(leagues) + LEARN_HTML
    out += "<details class='rp'><summary><b>Bu kurallar geçmişte ne kadar tuttu?</b> <span class='note'>(dokun)</span></summary>"
    out += rapor_bt_html(leagues).replace("<h3>Bu kurallar geçmişte ne kadar tuttu?</h3>", "") + "</details>"
    hours = [(d0 + dt.timedelta(hours=h)).astimezone(TR) for h in range(25)]
    opt_a = "".join(f"<option value='{h}'>{t:%H:%M}</option>" for h, t in enumerate(hours[:24]))
    opt_b = "".join(f"<option value='{h}'{' selected' if h == 24 else ''}>{t:%H:%M}{' (ertesi gün)' if h == 24 else ''}</option>"
                    for h, t in enumerate(hours) if h > 0)
    out += (f"<div class='tf' data-s='{int(d0.timestamp() * 1000)}'><span>Saat</span>"
            f"<select id='tf-a' onchange='rpFilter()'>{opt_a}</select><span>–</span>"
            f"<select id='tf-b' onchange='rpFilter()'>{opt_b}</select>"
            "<button onclick='tfNext(3)'>Sonraki 3 saat</button><button onclick='tfAll()'>Tümü</button></div>")
    chips = "<button data-k='main' class='on' onclick=\"rpShow('main')\">Günün önerileri</button>" + "".join(
        f"<button data-k='{k}' onclick=\"rpShow('{k}')\">{l}</button>" for k, l in RP_MARKETS) + \
        "<button data-k='done' onclick=\"rpShow('done')\">Başlayan / Biten</button>"
    out += f"<div class='rpchips'>{chips}</div>"
    order = lambda c, k: (-c["rapor"]["m"][k]["tier"], -c["rapor"]["m"][k]["score"])  # noqa
    mains = [(c, ln) for c, ln in cards if c["rapor"]["main"]]
    mains.sort(key=lambda x: order(x[0], x[0]["rapor"]["main"]))
    body = "".join(rp_item(c, c["rapor"]["main"], ln) for c, ln in mains)
    out += ("<div class='rps on' id='rps-main'><p class='note'>Öneri için hem kriterlerin çoğu tutmalı hem de model "
            f"en az %{MAIN_MIN_P * 100:.0f} ihtimal vermeli; ayrıca o bahis türü geçmişte gerçekten işe yaramış olmalı "
            "(1.5 Üst ve İY 0.5 Üst hariç). Her maçta varsa 2. öneri de yazılır. <b class='cnt'></b></p>"
            f"{body}<p class='empty none'>Seçilen saat aralığında başlamamış önerili maç yok.</p></div>")
    for key, label in RP_MARKETS:
        lst = [(c, ln) for c, ln in cards if key in c["rapor"]["m"] and not c["score"] and c["state"] == "pre"]
        lst.sort(key=lambda x: order(x[0], key))
        items = "".join(rp_item(c, key, ln, full=False) for c, ln in lst)
        out += (f"<div class='rps' id='rps-{key}'><p class='note'>{label}: seviyeye göre sıralı. <b class='cnt'></b></p>"
                f"{items}<p class='empty none'>Seçilen saat aralığında aday yok.</p></div>")
    fin = sorted(mains, key=lambda x: x[0]["kick"], reverse=True)
    fbody = "".join(rp_item(c, c["rapor"]["main"], ln) for c, ln in fin)
    out += ("<div class='rps' id='rps-done'><p class='note'>Başlamış ve bitmiş maçlardaki öneriler. Sonuçlar botun "
            f"her çalışmasında güncellenir. <b class='cnt'></b></p>{fbody}"
            "<p class='empty none'>Henüz başlayan önerili maç yok.</p></div>")
    return out


# ------------------------------------------------------------ T-1: dün ne dedik, ne oldu
T1_ROWS = [  # (etiket, olasılık anahtarı, üst/var adı, alt/yok adı, rapor anahtarı (üst), rapor anahtarı (alt))
    ("1.5 Ü/A", "o15", "1.5 Üst", "1.5 Alt", "o15", None),
    ("2.5 Ü/A", "o25", "2.5 Üst", "2.5 Alt", "o25", "u25"),
    ("3.5 Ü/A", "o35", "3.5 Üst", "3.5 Alt", "o35", None),
    ("4.5 Ü/A", "o45", "4.5 Üst", "4.5 Alt", "o45", None),
    ("KG", "btts", "KG Var", "KG Yok", "btts", None),
    ("İY 0.5 Ü/A", "iy05", "İY 0.5 Üst", "İY 0.5 Alt", "iy05", None),
    ("İY 1.5 Ü/A", "iy15", "İY 1.5 Üst", "İY 1.5 Alt", "iy15", None),
    ("İY KG", "iykg", "İY KG Var", "İY KG Yok", "iykg", None),
]
SURE = 0.65   # "emin olduğu" tahmin eşiği


def t1_lines(e):
    """Bir maç için her bahiste modelin eğilimi ve sonucu: (grup, tahmin metni, olasılık, doğru mu, rapor seviyesi)."""
    hg, ag, h1, a1 = e["res"]
    p, rpm = e["p"], e.get("rpm") or {}
    out = []
    ps = [p.get("p1", 0), p.get("px", 0), p.get("p2", 0)]
    k = max(range(3), key=lambda i: ps[i])
    tier = rpm.get({0: "ms1", 2: "ms2"}.get(k, ""), None)
    out.append(("MS", ["MS 1", "MS X", "MS 2"][k], ps[k], res3(hg, ag) == k, tier))
    for lab, key, up, down, rk_up, rk_down in T1_ROWS:
        q = p.get(key)
        if q is None:
            continue
        lean_up = q >= 0.5
        happened = outcome(key, e["res"]) if key not in ("iy05", "iy15", "iykg") or h1 is not None else None
        if happened is None:
            ok = None
        else:
            ok = happened == lean_up
        tier = rpm.get(rk_up if lean_up else (rk_down or ""), None)
        out.append((lab, up if lean_up else down, q if lean_up else 1 - q, ok, tier))
    ok = (e.get("ts") == f"{hg}-{ag}") if e.get("ts") else None
    out.append(("Skor", f"En olası skor {e['ts']}", None, ok, None))
    return out


def t1_tab(st, now):
    d0, _ = day_window(now)
    yd = d0 - dt.timedelta(days=1)
    yday = f"{yd:%Y-%m-%d}"
    ent = sorted([e for e in st["preds"].values() if e["d"] == yday and e.get("res")], key=lambda e: e["k"])
    out = (f"<h2>T-1 · Dün ({yd:%d.%m.%Y})</h2><p class='note'>Her maç için botun maç başlamadan önceki son tahmini "
           "ve gerçek sonuç. Her bahiste modelin ağır bastığı taraf (%50 üstü) gösterilir. Rozet varsa Gol "
           "Raporu o bahis için Güçlü/Orta demişti.</p>")
    if not ent:
        return out + "<p class='empty'>Dün için kayıtlı ve sonuçlanmış tahmin yok.</p>"
    rows = [(e, t1_lines(e)) for e in ent]
    # özet tablo
    agg = {}
    for _, lines in rows:
        for grp, _, prob, ok, tier in lines:
            a = agg.setdefault(grp, [0, 0, 0, 0, 0, 0])
            if ok is None:
                continue
            a[0] += ok
            a[1] += 1
            if prob is not None and prob >= SURE:
                a[2] += ok
                a[3] += 1
            if tier in (1, 2):
                a[4] += ok
                a[5] += 1

    def rc(h, t):
        return f"<td class='n'><b>%{h / t * 100:.0f}</b> <span class='note'>{h}/{t}</span></td>" if t else "<td class='n'>-</td>"
    out += ("<p class='note'><b>Tümü</b>: modelin her maçtaki eğilimi. <b>Emin</b>: modelin en az "
            f"%{SURE * 100:.0f} dediği tahminler. <b>Rozetli</b>: Gol Raporu'nun Güçlü/Orta dediği tahminler.</p>")
    out += (f"<div class='wrap'><table><tr><th>Bahis</th><th class='n'>Tümü</th>"
            f"<th class='n'>Emin (%{SURE * 100:.0f}+)</th><th class='n'>Rozetli</th></tr>")
    for grp in ["MS"] + [r[0] for r in T1_ROWS] + ["Skor"]:
        if grp in agg:
            a = agg[grp]
            out += f"<tr><td>{grp}</td>{rc(a[0], a[1])}{rc(a[2], a[3])}{rc(a[4], a[5])}</tr>"
    out += "</table></div>"
    # rapor önerileri
    rec = [(e, e["rp"]) for e in ent if e.get("rp")]
    if rec:
        hit = sum(1 for e, rp in rec if outcome(rp["c"], e["res"]))
        out += f"<h3>Gol Raporu önerileri: {hit}/{len(rec)} tuttu</h3><div class='wrap'><table><tr><th>Maç</th><th>Öneri</th><th class='n'>Skor</th><th class='n'>Sonuç</th></tr>"
        for e, rp in rec:
            o = outcome(rp["c"], e["res"])
            mark = "-" if o is None else ("<span class='pos'>✓</span>" if o else "<span class='neg'>✗</span>")
            out += (f"<tr><td>{E(e['h'])} - {E(e['a'])}</td><td><b>{GM_LABEL.get(rp['c'], rp['c'])}</b> "
                    f"<span class='tier t{rp['t']}'>{TIER_NAME[rp['t']]}</span></td>"
                    f"<td class='n'>{e['res'][0]}-{e['res'][1]}</td><td class='n'>{mark}</td></tr>")
        out += "</table></div>"
    # lig filtresi + maç listesi
    leagues_ = sorted({e["lg"] for e in ent})
    opts = "<option value=''>Tüm ligler</option>" + "".join(f"<option>{E(x)}</option>" for x in leagues_)
    out += (f"<h3>Maçlar ({len(ent)})</h3><div class='tf'><select id='t1lg' onchange='t1Filter()'>{opts}</select></div>")
    for e, lines in rows:
        hg, ag, h1, a1 = e["res"]
        k = dt.datetime.fromisoformat(e["k"]).astimezone(TR)
        good = sum(1 for x in lines if x[3] is True)
        tot = sum(1 for x in lines if x[3] is not None)
        ht = f" <span class='note'>(İY {h1}-{a1})</span>" if h1 is not None else ""
        rpl = ""
        if e.get("rp"):
            o = outcome(e["rp"]["c"], e["res"])
            rpl = (f"<div class='rb'>Rapor: <b>{GM_LABEL.get(e['rp']['c'], e['rp']['c'])}</b> "
                   f"<span class='tier t{e['rp']['t']}'>{TIER_NAME[e['rp']['t']]}</span> "
                   f"{'<span class=pos>✓</span>' if o else '<span class=neg>✗</span>'}</div>")
        body = "".join(
            f"<tr><td>{grp}</td><td>{E(txt)}{f' <span class=\"tier t{tier}\">{TIER_NAME[tier]}</span>' if tier in (1, 2) else ''}</td>"
            f"<td class='n'>{'' if prob is None else f'%{prob * 100:.0f}'}</td>"
            f"<td class='n'>{'-' if ok is None else ('<span class=pos>✓</span>' if ok else '<span class=neg>✗</span>')}</td></tr>"
            for grp, txt, prob, ok, tier in lines)
        out += (f"<details class='rp t1m' data-lg='{E(e['lg'])}'><summary>"
                f"<div class='rt'><span>{k:%H:%M} · {E(e['lg'])}</span><span>{good}/{tot} doğru</span></div>"
                f"<div class='rm'>{E(e['h'])} <b>{hg}-{ag}</b> {E(e['a'])}{ht}</div>{rpl}</summary>"
                f"<div class='wrap'><table><tr><th>Bahis</th><th>Model ne dedi</th><th class='n'>%</th><th class='n'>Sonuç</th></tr>"
                f"{body}</table></div></details>")
    miss = sum(1 for e in st["preds"].values() if e["d"] == yday and not e.get("res"))
    if miss:
        out += f"<p class='note'>{miss} maçın sonucu henüz işlenmedi; botun bir sonraki çalışmasında eklenecek.</p>"
    return out


# ------------------------------------------------------------ model günlüğü: dün → bugün ne öğrendi
def make_snapshot(leagues, now):
    lg = {}
    for L in leagues:
        m = L.get("model")
        if not m or L.get("err"):
            continue
        hm = m.get("half") or {}
        lg[L["name"]] = {"n": L["nfin"], "ny": L.get("ny", 0), "ha": round(m["ha"] ** 2, 3), "f": round(hm.get("f", 0), 3),
                         "rho": m["rho"], "k": (L.get("kc") or (0, 0))[0], "c": (L.get("kc") or (0, 0))[1],
                         "g90": round(L["avg90"], 2) if L.get("avg90") else None, "xw": L.get("xw", 0.0)}
    tr = {f"{k}/{t}": [round(v["hit"], 3), v["n"], v["ok"], round(v["base"], 3)] for (k, t), v in (TRUST or {}).items()}
    return {"t": now.isoformat(), "leagues": lg, "trust": tr, "nmatch": sum(x["n"] for x in lg.values())}


def snapshot_from_html(path="index.html"):
    """Önceki çalışmanın yayınladığı sayfadan model durumunu okur (günlük henüz yoksa)."""
    try:
        s = open(path, encoding="utf-8").read()
    except Exception:  # noqa
        return None
    snap = {"t": "", "leagues": {}, "trust": {}, "nmatch": 0, "src": "sayfa"}
    try:
        i = s.index("Model parametreleri")
        t = s[i:s.index("</table>", i)]
        for row in re.findall(r"<tr>(.*?)</tr>", t):
            c = [html.unescape(re.sub("<[^>]+>", "", x)).strip() for x in re.findall(r"<t[hd][^>]*>(.*?)</t[hd]>", row)]
            if len(c) < 7 or c[0] == "Lig":
                continue
            snap["leagues"][c[0]] = {"n": None, "ha": float(c[1]), "f": float(c[2].strip("%")) / 100 if c[2] != "-" else 0,
                                     "rho": float(c[3]), "k": float(c[5].strip("*")), "c": float(c[6]), "g90": None}
        for name, n in re.findall(r"<h2>([^<]+)</h2>\s*<p class='row'>(\d+) geçmiş maç verisi", s):
            name = html.unescape(name)
            if name in snap["leagues"]:
                snap["leagues"][name]["n"] = int(n)
        inv = {v: k for k, v in GM_LABEL.items()}
        for tier, lab, hit, n, base in re.findall(
                r"Geçmiş: (Güçlü|Orta) ([^<]+?) önerileri <b class='\w+'>%(\d+)</b> tuttu \((\d+) maç; tüm maçlarda %(\d+)\)", s):
            k = inv.get(html.unescape(lab))
            if k:
                t_ = 2 if tier == "Güçlü" else 1
                snap["trust"][f"{k}/{t_}"] = [int(hit) / 100, int(n), None, int(base) / 100]
        snap["nmatch"] = sum(x["n"] or 0 for x in snap["leagues"].values())
    except Exception:  # noqa
        return None
    return snap if snap["leagues"] else None


def update_log(st, snap, prev_html, now):
    d0, _ = day_window(now)
    day = f"{d0:%Y-%m-%d}"
    log = st.setdefault("log", {})
    if not any(k < day for k in log) and prev_html:
        yd = f"{d0 - dt.timedelta(days=1):%Y-%m-%d}"
        log[yd] = prev_html
    log[day] = snap
    for k in sorted(log)[:-60]:
        del log[k]


def learn_html(st, now):
    d0, _ = day_window(now)
    day = f"{d0:%Y-%m-%d}"
    log = st.get("log", {})
    cur = log.get(day)
    prevs = [k for k in sorted(log) if k < day]
    if not cur or not prevs:
        return ""
    pd_ = prevs[-1]
    prev = log[pd_]
    out = (f"<div class='card'><h2>Model dün ne öğrendi?</h2><p class='note'>{pd_[8:]}.{pd_[5:7]} durumu ile "
           f"bugünkü durum karşılaştırması. Bunlar botun yeni sonuçlardan kendiliğinden çıkardığı değişikliklerdir.</p>")
    common = [n for n in cur["leagues"] if n in prev["leagues"]]
    added = sum((cur["leagues"][n]["n"] or 0) - (prev["leagues"][n]["n"] or 0) for n in common
                if prev["leagues"][n]["n"] is not None)
    newl = [n for n in cur["leagues"] if n not in prev["leagues"]]
    ny = sum(x.get("ny", 0) for x in cur["leagues"].values())
    out += (f"<div class='row'>Dün biten ve modele eklenen maç: <b>{ny}</b> · modelin kullandığı toplam maç: "
            f"{cur['nmatch']} (son ~14 ay; en eski maçlar pencereden düşer)</div>")
    if newl:
        out += f"<div class='row'>Yeni eklenen lig: <b>{E(', '.join(newl))}</b></div>"
    # güven filtresi değişimleri
    rows, on, off = [], [], []
    for key, v in sorted(cur["trust"].items()):
        p = prev["trust"].get(key)
        k, t = key.split("/")
        lab = f"{TIER_NAME[int(t)].capitalize()} {GM_LABEL.get(k, k)}"
        if p and p[2] is not None and p[2] != v[2]:
            (on if v[2] else off).append(lab)
        if p and v[1] >= TRUST_MIN_N:
            dh = (v[0] - p[0]) * 100
            rows.append((abs(dh), lab, p, v, dh))
    if on:
        out += f"<div class='row'>Güven filtresi açtı (artık önerilebilir): <b class='pos'>{E(', '.join(on))}</b></div>"
    if off:
        out += f"<div class='row'>Güven filtresi kapattı (artık önerilmez): <b class='neg'>{E(', '.join(off))}</b></div>"
    if rows:
        rows.sort(key=lambda x: -x[0])
        out += ("<div class='sec'>Bahis türlerinin geçmiş isabeti (dün → bugün)</div><div class='wrap'><table>"
                "<tr><th>Öneri</th><th class='n'>Dün</th><th class='n'>Bugün</th><th class='n'>Fark</th></tr>")
        for _, lab, p, v, dh in rows[:10]:
            cls_ = "pos" if dh > 0.5 else ("neg" if dh < -0.5 else "")
            out += (f"<tr><td>{E(lab)}</td><td class='n'>%{p[0] * 100:.0f} <span class='note'>({p[1]})</span></td>"
                    f"<td class='n'>%{v[0] * 100:.0f} <span class='note'>({v[1]})</span></td>"
                    f"<td class='n {cls_}'>{dh:+.1f}</td></tr>")
        out += "</table></div>"
    # lig parametreleri
    ch = []
    for n in common:
        a, b = prev["leagues"][n], cur["leagues"][n]
        notes = []
        if abs(b["ha"] - a["ha"]) >= 0.01:
            notes.append(f"ev avantajı {a['ha']:.2f}→{b['ha']:.2f}")
        if a["f"] and abs(b["f"] - a["f"]) >= 0.01:
            notes.append(f"ilk yarı gol payı %{a['f'] * 100:.0f}→%{b['f'] * 100:.0f}")
        if abs(b["rho"] - a["rho"]) >= 0.01:
            notes.append(f"beraberlik eğilimi {a['rho']:+.2f}→{b['rho']:+.2f}")
        if b.get("xw") is not None and a.get("xw") is not None and abs(b["xw"] - a["xw"]) >= 0.01:
            notes.append(f"şut ağırlığı {a['xw']:.2f}→{b['xw']:.2f}")
        if abs(b["c"] - a["c"]) >= 0.01 or abs(b["k"] - a["k"]) >= 0.01:
            notes.append(f"yüzde ayarı k {a['k']:.2f}→{b['k']:.2f}, c {a['c']:.2f}→{b['c']:.2f}")
        if notes:
            ch.append(f"<b>{E(n)}</b>: " + ", ".join(notes))
    if ch:
        out += "<div class='sec'>Liglerde değişen ayarlar</div>" + "".join(f"<div class='row'>{x}</div>" for x in ch)
    else:
        out += ("<div class='row'>Lig ayarlarında belirgin değişiklik yok: birkaç günlük yeni sonuç, yüzlerce maçlık "
                "geçmişi çok az kaydırır. Asıl öğrenme takım güçlerinde ve bahis türlerinin isabetinde görünür.</div>")
    return out + "</div>"


# ------------------------------------------------------------ bahislerim: kupon kaydı ve kazanç analizi
BET_FROM = "2026-10-15"     # maç listesinin başlangıcı (geçmiş kuponları girme dönemi)
BET_DAILY = True            # True olunca kayıt sayfası sadece dün/bugün/yarın maçlarını gösterir
BET_FILE = "data/bahislerim.json"
MAC_FILE = "data/maclar.json"
BET_LINES = ["05", "15", "25", "35", "45", "55"]
BET_MARKETS = (
    [("Maç sonucu", c, l) for c, l in (("ms1", "MS 1"), ("msx", "MS X"), ("ms2", "MS 2"))]
    + [("Çifte şans", c, l) for c, l in (("cs1x", "Çifte şans 1-X"), ("cs12", "Çifte şans 1-2"), ("csx2", "Çifte şans X-2"))]
    + [("Alt / Üst", f"{p}{x}", f"{x[0]}.5 {'Üst' if p == 'o' else 'Alt'}") for x in BET_LINES for p in "ou"]
    + [("Karşılıklı gol", "kgv", "KG Var"), ("Karşılıklı gol", "kgy", "KG Yok")]
    + [("İlk yarı", c, l) for c, l in (("iy1", "İY 1"), ("iyx", "İY X"), ("iy2", "İY 2"))]
    + [("İlk yarı", f"iy{p}{x}", f"İY {x[0]}.5 {'Üst' if p == 'o' else 'Alt'}") for x in ("05", "15", "25") for p in "ou"]
    + [("İlk yarı", "iykgv", "İY KG Var"), ("İlk yarı", "iykgy", "İY KG Yok")]
    + [("Takım golü", f"t{h}{t}{x}", f"{'Ev' if t == 'ev' else 'Dep'} {'İY ' if h else ''}{x[0]}.5 Üst")
       for h in ("", "i") for t in ("ev", "dp") for x in (("05", "15", "25") if not h else ("05", "15"))]
    + [("İY / MS", f"im{a}{b}", f"İY/MS {a.upper()}/{b.upper()}") for a in "1x2" for b in "1x2"]
    + [("MS ve 2.5 Alt/Üst", f"ms{r}+{p}25", f"MS {r.upper()} ve 2.5 {'Üst' if p == 'o' else 'Alt'}")
       for r in "1x2" for p in "ou"]
    + [("Maç skoru", f"sk{h}-{a}", f"Skor {h}-{a}") for h in range(5) for a in range(5)]
    + [("Diğer", "diger", "Diğer (sonucu ben gireceğim)")]
)
BET_LABEL = {c: l for _, c, l in BET_MARKETS}
BET_TO_RAPOR = {"ms1": "ms1", "ms2": "ms2", "o15": "o15", "o25": "o25", "o35": "o35", "o45": "o45", "u25": "u25",
                "kgv": "btts", "iyo05": "iy05", "iyo15": "iy15", "iykgv": "iykg",
                "tev05": "h05", "tdp05": "a05", "tev15": "h15", "tdp15": "a15", "tiev05": "ih05", "tidp05": "ia05"}


def bet_settle(code, res):
    """True/False, sonuç yoksa ya da manuel bahisse None. res = [hg, ag, h1, a1]."""
    if not res or res[0] is None or code == "diger":
        return None
    if "+" in code:                       # birleşik bahis: hepsi tutmalı
        parts = [bet_settle(c, res) for c in code.split("+")]
        return None if None in parts else all(parts)
    hg, ag, h1, a1 = res
    tm_ = re.match(r"^t(i?)(ev|dp)(\d)(\d)$", code)
    if tm_:
        ln = int(tm_.group(3)) + 0.5
        if tm_.group(1):
            if h1 is None or a1 is None:
                return None
            g = h1 if tm_.group(2) == "ev" else a1
        else:
            g = hg if tm_.group(2) == "ev" else ag
        return g > ln
    if code.startswith("sk"):
        h, a = code[2:].split("-")
        return hg == int(h) and ag == int(a)
    r = res3(hg, ag)
    if code in ("ms1", "msx", "ms2"):
        return r == {"ms1": 0, "msx": 1, "ms2": 2}[code]
    if code.startswith("cs"):
        return r in {"cs1x": (0, 1), "cs12": (0, 2), "csx2": (1, 2)}[code]
    if code[0] in "ou" and code[1:].isdigit():
        ln = int(code[1]) + 0.5
        return hg + ag > ln if code[0] == "o" else hg + ag < ln
    if code == "kgv":
        return hg > 0 and ag > 0
    if code == "kgy":
        return not (hg > 0 and ag > 0)
    if h1 is None or a1 is None:
        return None
    r1 = res3(h1, a1)
    if code in ("iy1", "iyx", "iy2"):
        return r1 == {"iy1": 0, "iyx": 1, "iy2": 2}[code]
    if code.startswith("iyo") or code.startswith("iyu"):
        ln = int(code[3]) + 0.5
        return h1 + a1 > ln if code[2] == "o" else h1 + a1 < ln
    if code == "iykgv":
        return h1 > 0 and a1 > 0
    if code == "iykgy":
        return not (h1 > 0 and a1 > 0)
    if code.startswith("im"):
        m = {"1": 0, "x": 1, "2": 2}
        return r1 == m[code[2]] and r == m[code[3]]
    return None


def load_bets():
    try:
        with open(BET_FILE, encoding="utf-8") as f:
            d = json.load(f)
        d.setdefault("kuponlar", [])
        return d
    except Exception:  # noqa
        return {"kuponlar": []}


def write_maclar(leagues, now):
    start = dt.datetime.fromisoformat(BET_FROM).replace(tzinfo=TR)
    if BET_DAILY:
        start = max(start, now - dt.timedelta(days=2))
    end = now + dt.timedelta(days=2)
    bet_ids = {str(l.get("m")) for k in load_bets()["kuponlar"] for l in k["legs"] if l.get("m")}
    rows, seen = [], set()
    md = {}
    for L in leagues:
        for c in L.get("cards", []):
            r = c["r"]
            lam1 = r.get("lam1") or [c["lam"][0] * 0.45, c["lam"][1] * 0.45]
            md[c["id"]] = {"l": [round(x, 4) for x in (c["lam"][0], c["lam"][1], lam1[0], lam1[1])],
                           "p": {k: round(r[k], 4) for k in PRED_KEYS if r.get(k) is not None}}
    for L in leagues:
        for m in L.get("allm", L.get("allm_bet", [])):
            if m["id"] in seen or not ((start <= m["date"] <= end) or m["id"] in bet_ids):
                continue
            seen.add(m["id"])
            ht = m.get("ht") or (None, None)
            rows.append({"id": m["id"], "k": m["date"].isoformat(), "lg": L["name"], "h": m["home"], "a": m["away"],
                         "s": [m["hg"], m["ag"], ht[0], ht[1]] if m["done"] else None})
            if m["id"] in md and not m["done"]:
                rows[-1]["md"] = md[m["id"]]
    rows.sort(key=lambda x: x["k"])
    os.makedirs("data", exist_ok=True)
    with open(MAC_FILE, "w", encoding="utf-8") as f:
        dbg = {L["name"]: [len(L.get("allm_bet", [])), L.get("nall", 0),
                           min((m["date"] for m in L.get("allm_bet", [])), default=now).isoformat()[:10]] for L in leagues}
        json.dump({"t": now.isoformat(), "from": BET_FROM, "daily": BET_DAILY, "maclar": rows, "dbg": dbg},
                  f, ensure_ascii=False, separators=(",", ":"))
    return {r["id"]: r for r in rows}


def bet_leg_result(leg, macs):
    if leg.get("sonuc") in ("tuttu", "yatti"):
        return leg["sonuc"] == "tuttu"
    m = macs.get(str(leg.get("m"))) if leg.get("m") else None
    return bet_settle(leg.get("b"), m["s"]) if m and m.get("s") else None


def coupon_state(kp, macs):
    rs = [bet_leg_result(l, macs) for l in kp["legs"]]
    odds = 1.0
    for l in kp["legs"]:
        odds *= float(l.get("o") or 1)
    if any(r is False for r in rs):
        st_ = "yatti"
    elif all(r is True for r in rs) and rs:
        st_ = "tuttu"
    else:
        st_ = "bekliyor"
    return st_, rs, odds


BET_PMAP = {"ms1": "p1", "msx": "px", "ms2": "p2", "o15": "o15", "o25": "o25", "o35": "o35", "o45": "o45",
            "kgv": "btts", "iyo05": "iy05", "iyo15": "iy15", "iykgv": "iykg",
            "tev05": "h05", "tdp05": "a05", "tev15": "h15", "tdp15": "a15", "tiev05": "ih05", "tidp05": "ia05"}
BET_PNEG = {"u15": "o15", "u25": "o25", "u35": "o35", "u45": "o45", "kgy": "btts", "iyu05": "iy05",
            "iyu15": "iy15", "iykgy": "iykg"}


def bet_model_p(code, p):
    """Bahis kodu için modelin maç öncesi olasılığı (p: kayıtlı tahmin olasılıkları). Bilinmiyorsa None."""
    if not p or not code:
        return None
    if "+" in code:
        return None
    if code in BET_PMAP and p.get(BET_PMAP[code]) is not None:
        return p[BET_PMAP[code]]
    if code in BET_PNEG and p.get(BET_PNEG[code]) is not None:
        return 1 - p[BET_PNEG[code]]
    if code.startswith("cs") and None not in (p.get("p1"), p.get("px"), p.get("p2")):
        return {"cs1x": p["p1"] + p["px"], "cs12": p["p1"] + p["p2"], "csx2": p["px"] + p["p2"]}.get(code)
    return None


def leg_mp(l, preds):
    if l.get("mp") is not None:
        return float(l["mp"])
    if l.get("canli"):
        return None
    return bet_model_p(l.get("b"), (preds.get(str(l.get("m"))) or {}).get("p"))


def bets_tab(st, macs):
    data = load_bets()
    kps = data["kuponlar"]
    out = ("<h2>Bahislerim</h2><p class='note'>Kayıtlı kuponların ve oynadığın bahislerin analizi. Yeni kupon "
           "girmek için <a href='bahis.html'>kupon kayıt sayfasını</a> aç. Sonuçlar botun her çalışmasında "
           "(08:00, 14:00, 23:30) güncellenir.</p>")
    if not kps:
        return out + "<p class='empty'>Henüz kayıtlı kupon yok.</p>"
    stake = ret = 0.0
    n_done = n_win = 0
    legs = []
    for kp in kps:
        s_, rs, odds = coupon_state(kp, macs)
        t = float(kp.get("tutar") or 0)
        if s_ != "bekliyor":
            n_done += 1
            stake += t
            if s_ == "tuttu":
                n_win += 1
                ret += t * odds
        for l, r in zip(kp["legs"], rs):
            legs.append((l, r))
    net = ret - stake
    roi = net / stake * 100 if stake else 0
    out += (f"<div class='grid'><div class='b lo'>Kupon<br><b>{n_win}/{n_done}</b><small>tutan / sonuçlanan</small></div>"
            f"<div class='b lo'>Yatırılan<br><b>{stake:,.0f}</b><small>TL</small></div>"
            f"<div class='b {'hi' if net > 0 else 'lo'}'>Net<br><b>{net:+,.0f}</b><small>ROI %{roi:+.0f}</small></div></div>")

    def group_rows(title, keyf):
        g = defaultdict(lambda: [0, 0, 0.0])
        for l, r in legs:
            if r is None:
                continue
            k = keyf(l)
            g[k][0] += r
            g[k][1] += 1
            g[k][2] += 1 / max(float(l.get("o") or 1), 1.01)
        if not g:
            return ""
        h = (f"<div class='sec'>{title}</div><div class='wrap'><table><tr><th></th><th class='n'>Bacak</th>"
             "<th class='n'>Tuttu</th><th class='n'>Gereken</th></tr>")
        for k, (w, n, need) in sorted(g.items(), key=lambda kv: -kv[1][1]):
            hit, nd = w / n, need / n
            cls_ = "pos" if hit > nd + 0.02 else ("neg" if hit < nd - 0.02 else "")
            h += (f"<tr><td>{E(k)}</td><td class='n'>{n}</td><td class='n {cls_}'>%{hit * 100:.0f}</td>"
                  f"<td class='n'>%{nd * 100:.0f}</td></tr>")
        return h + "</table></div>"

    preds = st.get("preds", {})

    def rapor_of(l):
        rk = BET_TO_RAPOR.get(l.get("b"))
        tier = ((preds.get(str(l.get("m"))) or {}).get("rpm") or {}).get(rk) if rk else None
        return {2: "Rapor: Güçlü", 1: "Rapor: Orta", 0: "Rapor: Zayıf"}.get(tier, "Raporda yok")

    def band(l):
        o = float(l.get("o") or 0)
        return "1.50 altı" if o < 1.5 else ("1.50-1.99" if o < 2 else ("2.00-2.99" if o < 3 else "3.00+"))
    # Model ne diyordu? (sadece maç öncesi bacaklar, modelin olasılığı bilinen kuponlar)
    preds_ = st.get("preds", {})
    exp_w = act_w = n_k = 0
    lg_band = defaultdict(lambda: [0, 0])
    for kp in kps:
        s_, rs, _ = coupon_state(kp, macs)
        mps = [leg_mp(l, preds_) for l in kp["legs"]]
        for mp, r in zip(mps, rs):
            if mp is not None and r is not None:
                b_ = "Model %60+" if mp >= 0.6 else ("Model %50-59" if mp >= 0.5 else "Model %50 altı")
                lg_band[b_][0] += r
                lg_band[b_][1] += 1
        if s_ != "bekliyor" and mps and None not in mps:
            pr = 1.0
            for x in mps:
                pr *= x
            exp_w += pr
            act_w += s_ == "tuttu"
            n_k += 1
    if lg_band:
        out += ("<div class='sec'>Model ne diyordu?</div><p class='note'>Maç öncesi oynadığın bacaklar, modelin o bahse "
                "verdiği ihtimale göre gruplandı. Kuponun birlikte tutma ihtimali = bacak ihtimallerinin çarpımı.</p>"
                "<div class='wrap'><table><tr><th></th><th class='n'>Bacak</th><th class='n'>Tuttu</th></tr>")
        for b_ in ("Model %60+", "Model %50-59", "Model %50 altı"):
            if b_ in lg_band:
                w_, n_ = lg_band[b_]
                out += f"<tr><td>{b_}</td><td class='n'>{n_}</td><td class='n'>%{w_ / n_ * 100:.0f}</td></tr>"
        out += "</table></div>"
        if n_k:
            out += (f"<p class='note'>Tüm bacaklarında model verisi olan {n_k} sonuçlanmış kupon için model toplamda "
                    f"<b>{exp_w:.1f}</b> kupon tutmasını bekliyordu; tutan: <b>{act_w}</b>.</p>")
    out += ("<p class='note'><b>Gereken</b>: o bahislerin oranlarına göre kâra geçmek için tutması gereken oran. "
            "Tuttu sütunu bunun üstündeyse (yeşil) o tür bahisler tekli oynansaydı kazandırırdı.</p>")
    out += group_rows("Bahis türüne göre", lambda l: BET_LABEL.get(l.get("b"), l.get("bl") or "?"))
    out += group_rows("Canlı / maç öncesi", lambda l: "Canlı" if l.get("canli") else "Maç öncesi")
    out += group_rows("Gol Raporu ile uyum", rapor_of)
    out += group_rows("Oran aralığına göre", band)
    out += "<div class='sec'>Kuponlar</div>"
    for kp in sorted(kps, key=lambda k: k.get("t", ""), reverse=True)[:40]:
        s_, rs, odds = coupon_state(kp, macs)
        t = float(kp.get("tutar") or 0)
        lab = {"tuttu": "<span class='pos'>Kazandı</span>", "yatti": "<span class='neg'>Kaybetti</span>",
               "bekliyor": "Bekliyor"}[s_]
        rows = "".join(
            f"<tr><td>{E(l.get('ad', ''))}{' <span class=note>(canlı)</span>' if l.get('canli') else ''}</td>"
            f"<td>{E(BET_LABEL.get(l.get('b'), l.get('bl') or ''))}</td><td class='n'>{float(l.get('o') or 0):.2f}</td>"
            f"<td class='n'>{'⏳' if r is None else ('<span class=pos>✓</span>' if r else '<span class=neg>✗</span>')}</td></tr>"
            for l, r in zip(kp["legs"], rs))
        out += (f"<details class='rp'><summary><div class='rt'><span>{E(kp.get('t', '')[:10])} · {len(kp['legs'])} maç</span>"
                f"<span>{lab}</span></div><div class='rb'>{t:,.0f} TL × {odds:.2f} = <b>{t * odds:,.0f} TL</b></div></summary>"
                f"<div class='wrap'><table><tr><th>Maç</th><th>Bahis</th><th class='n'>Oran</th><th class='n'></th></tr>"
                f"{rows}</table></div></details>")
    return out


BET_CSS = """
.wrapb{padding:4px 12px 40px}
.top{display:flex;justify-content:space-between;align-items:center;gap:8px}
.back{color:var(--ac);text-decoration:none;font-size:14px;font-weight:600}
.in,.sel{width:100%;font-size:16px;padding:10px;border-radius:10px;border:1px solid var(--bd);background:var(--bg);color:var(--tx)}
.row2{display:flex;gap:8px;margin-top:8px}.row2>*{flex:1}
.btn{border:1px solid var(--bd);background:var(--card);color:var(--tx);border-radius:10px;padding:10px 12px;font-size:15px;font-weight:600}
.btn.pri{background:var(--ac);border-color:var(--ac);color:#fff}
.btn.sm{padding:6px 10px;font-size:13px;border-radius:8px}
.btn.on{background:var(--tx);color:var(--bg);border-color:var(--tx)}
.mlist{max-height:46vh;overflow-y:auto;margin-top:8px;border-radius:10px;border:1px solid var(--bd)}
.mi{display:block;width:100%;text-align:left;background:var(--card);color:var(--tx);border:0;border-bottom:1px solid var(--bd);padding:9px 10px;font-size:14px}
.mi small{display:block;color:var(--mu);font-size:12px}
.mi b.sc{float:right}
.legf{border:2px solid var(--ac);border-radius:12px;padding:10px;margin-top:10px}
.leg{display:flex;justify-content:space-between;align-items:center;gap:8px;border-bottom:1px solid var(--bd);padding:7px 0;font-size:14px}
.mp{margin-top:6px;font-size:13px;color:var(--mu)}.mp b{color:var(--tx)}
.leg small{display:block;color:var(--mu);font-size:12px}
.tot{font-size:15px;margin:10px 0}
.msg{font-size:14px;margin-top:8px}
.kp{background:var(--card);border-radius:12px;padding:10px 12px;margin-bottom:8px}
.kh{display:flex;justify-content:space-between;font-size:13px;color:var(--mu)}
details.kp summary{list-style:none;cursor:pointer}details.kp summary::-webkit-details-marker{display:none}
.ks{font-size:14px;margin-top:3px}details.kp[open] .ks{display:none}
"""

BET_JS = r"""
const REPO = __REPO__, MARKETS = __MARKETS__, API = 'https://api.github.com/repos/'+REPO+'/contents/data/bahislerim.json';
let MACS = [], MBY = {}, DATA = {kuponlar:[]}, DAILY = false, FROM = '';
let draft = [], pick = null, canli = false;
const $ = id => document.getElementById(id);
function esc(s){return String(s==null?'':s).replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));}
function tok(){ try{return localStorage.getItem('nb_token')||'';}catch(e){return '';} }
function dayOf(iso){ return new Date(iso).toLocaleDateString('sv-SE',{timeZone:'Europe/Istanbul'}); }
function hm(iso){ return new Date(iso).toLocaleTimeString('tr-TR',{hour:'2-digit',minute:'2-digit',timeZone:'Europe/Istanbul'}); }
function dm(day){ return day.slice(8)+'.'+day.slice(5,7); }
function b64e(s){ return btoa(unescape(encodeURIComponent(s))); }
function b64d(b){ return decodeURIComponent(escape(atob(b.replace(/\s/g,'')))); }
function res3(h,a){ return h>a?0:(h===a?1:2); }
function settle(code, s){
  if(!s || s[0]==null || code==='diger') return null;
  if(code.includes('+')){ const p = code.split('+').map(c=>settle(c,s)); return p.includes(null) ? null : p.every(x=>x); }
  const [hg,ag,h1,a1] = s, r = res3(hg,ag);
  const tm = code.match(/^t(i?)(ev|dp)(\d)(\d)$/);
  if(tm){ const ln = +tm[3]+0.5; if(tm[1]){ if(h1==null||a1==null) return null; return (tm[2]==='ev'?h1:a1) > ln; } return (tm[2]==='ev'?hg:ag) > ln; }
  if(code.startsWith('sk')){ const [h,a] = code.slice(2).split('-').map(Number); return hg===h && ag===a; }
  if(code==='ms1') return r===0; if(code==='msx') return r===1; if(code==='ms2') return r===2;
  if(code==='cs1x') return r!==2; if(code==='cs12') return r!==1; if(code==='csx2') return r!==0;
  if(/^[ou]\d\d$/.test(code)){ const ln=+code[1]+0.5; return code[0]==='o' ? hg+ag>ln : hg+ag<ln; }
  if(code==='kgv') return hg>0&&ag>0; if(code==='kgy') return !(hg>0&&ag>0);
  if(h1==null||a1==null) return null;
  const r1 = res3(h1,a1);
  if(code==='iy1') return r1===0; if(code==='iyx') return r1===1; if(code==='iy2') return r1===2;
  if(/^iy[ou]\d\d$/.test(code)){ const ln=+code[3]+0.5; return code[2]==='o' ? h1+a1>ln : h1+a1<ln; }
  if(code==='iykgv') return h1>0&&a1>0; if(code==='iykgy') return !(h1>0&&a1>0);
  if(code.startsWith('im')){ const m={'1':0,'x':1,'2':2}; return r1===m[code[2]] && r===m[code[3]]; }
  return null;
}
function pois(k,l){let p=Math.exp(-l);for(let i=1;i<=k;i++)p*=l/i;return p;}
const PMAP={ms1:'p1',msx:'px',ms2:'p2',o15:'o15',o25:'o25',o35:'o35',o45:'o45',kgv:'btts',iyo05:'iy05',iyo15:'iy15',iykgv:'iykg',
            tev05:'h05',tdp05:'a05',tev15:'h15',tdp15:'a15',tiev05:'ih05',tidp05:'ia05'};
const PNEG={u15:'o15',u25:'o25',u35:'o35',u45:'o45',kgy:'btts',iyu05:'iy05',iyu15:'iy15',iykgy:'iykg'};
// Modelin maç öncesi olasılığı: biliniyorsa modelin kendi değeri, yoksa gol beklentilerinden (ilk yarı / ikinci yarı) hesap
function modelP(code, md){
  if(!md || !code || code==='diger') return null;
  const p = md.p || {};
  if(!code.includes('+')){
    if(PMAP[code] && p[PMAP[code]]!=null) return p[PMAP[code]];
    if(PNEG[code] && p[PNEG[code]]!=null) return 1-p[PNEG[code]];
    if(code==='cs1x' && p.p1!=null) return p.p1+p.px;
    if(code==='cs12' && p.p1!=null) return p.p1+p.p2;
    if(code==='csx2' && p.px!=null) return p.px+p.p2;
  }
  if(!md.l) return null;
  const [lh,la,lh1,la1] = md.l, lh2 = Math.max(lh-lh1,0.01), la2 = Math.max(la-la1,0.01), N = 8;
  const A=[],B=[],C=[],D=[];
  for(let i=0;i<N;i++){A.push(pois(i,lh1));B.push(pois(i,la1));C.push(pois(i,lh2));D.push(pois(i,la2));}
  let s=0, t=0;
  for(let h1=0;h1<N;h1++) for(let a1=0;a1<N;a1++){ const q=A[h1]*B[a1]; if(q<1e-9) continue;
    for(let h2=0;h2<N;h2++) for(let a2=0;a2<N;a2++){ const pr=q*C[h2]*D[a2]; t+=pr; const v=settle(code,[h1+h2,a1+a2,h1,a1]); if(v===null) return null; if(v) s+=pr; } }
  return t ? s/t : null;
}
function pc(x){ return '%'+(x*100<1 ? (x*100).toFixed(1) : Math.round(x*100)); }
function legRes(l){ if(l.sonuc==='tuttu') return true; if(l.sonuc==='yatti') return false;
  const m = l.m ? MBY[l.m] : null; return m && m.s ? settle(l.b, m.s) : null; }
function kState(k){ const rs = k.legs.map(legRes); let o=1; k.legs.forEach(l=>o*=+l.o||1);
  return {st: rs.some(r=>r===false)?'yatti':(rs.length&&rs.every(r=>r===true)?'tuttu':'bekliyor'), rs, o}; }

async function ghLoad(){
  const r = await fetch(API+'?ref=main&t='+Date.now(), {headers:{Authorization:'Bearer '+tok(), Accept:'application/vnd.github+json'}, cache:'no-store'});
  if(r.status===404) return {data:{kuponlar:[]}, sha:null};
  if(!r.ok) throw new Error('GitHub '+r.status+(r.status===401?' (anahtar geçersiz)':''));
  const j = await r.json(); return {data: JSON.parse(b64d(j.content)), sha: j.sha};
}
async function ghSave(mut, msg){
  if(!tok()) throw new Error('Önce aşağıdaki Ayarlar bölümünden GitHub anahtarını gir.');
  for(let i=0;i<3;i++){
    const {data, sha} = await ghLoad(); data.kuponlar = data.kuponlar||[]; mut(data);
    const body = {message: msg, content: b64e(JSON.stringify(data, null, 1)), branch:'main'}; if(sha) body.sha = sha;
    const r = await fetch(API, {method:'PUT', headers:{Authorization:'Bearer '+tok(), Accept:'application/vnd.github+json', 'Content-Type':'application/json'}, body: JSON.stringify(body)});
    if(r.ok){ DATA = data; return; }
    if(r.status!==409 && r.status!==422) throw new Error('Kaydedilemedi: GitHub '+r.status);
  }
  throw new Error('Kaydedilemedi, tekrar dene.');
}
function msg(t, ok){ const e=$('msg'); e.innerHTML = t; e.style.color = ok ? 'var(--ac)' : 'var(--neg)'; }

function renderSummary(){
  let n=0,w=0,stake=0,ret=0,pend=0;
  for(const k of DATA.kuponlar){ const s=kState(k), t=+k.tutar||0;
    if(s.st==='bekliyor'){ pend++; continue; } n++; stake+=t; if(s.st==='tuttu'){ w++; ret+=t*s.o; } }
  const net = ret-stake;
  $('sum').innerHTML = '<div class="grid"><div class="b lo">Kupon<br><b>'+w+'/'+n+'</b><small>tutan · '+pend+' bekliyor</small></div>'+
    '<div class="b lo">Yatırılan<br><b>'+Math.round(stake).toLocaleString('tr-TR')+'</b><small>TL</small></div>'+
    '<div class="b '+(net>0?'hi':'lo')+'">Net<br><b>'+(net>=0?'+':'')+Math.round(net).toLocaleString('tr-TR')+'</b><small>'+(stake?('ROI %'+Math.round(net/stake*100)):'')+'</small></div></div>';
}
function renderDays(){
  const days = [...new Set(MACS.map(m=>dayOf(m.k)))].sort();
  const today = dayOf(new Date().toISOString());
  $('day').innerHTML = days.map(d=>'<option value="'+d+'"'+(d===today?' selected':'')+'>'+dm(d)+(d===today?' (bugün)':'')+'</option>').join('');
}
function renderList(){
  const q = $('q').value.trim().toLocaleLowerCase('tr-TR'), d = $('day').value;
  let ms = MACS.filter(m => q ? (m.h+' '+m.a+' '+m.lg).toLocaleLowerCase('tr-TR').includes(q) : dayOf(m.k)===d);
  if(q) ms = ms.slice(-60);
  $('ml').innerHTML = ms.map(m=>'<button class="mi" onclick="pickM(\''+m.id+'\')"><b class="sc">'+(m.s?m.s[0]+'-'+m.s[1]:'')+'</b>'+
    esc(m.h)+' - '+esc(m.a)+'<small>'+(q?dm(dayOf(m.k))+' ':'')+hm(m.k)+' · '+esc(m.lg)+'</small></button>').join('') ||
    '<p class="empty" style="padding:10px">Maç bulunamadı.</p>';
}
function mkSelect(){
  let h='', g='';
  for(const [grp,c,l] of MARKETS){ if(grp!==g){ if(g) h+='</optgroup>'; h+='<optgroup label="'+grp+'">'; g=grp; } h+='<option value="'+c+'">'+esc(l)+'</option>'; }
  return h+'</optgroup>';
}
function pickM(id){
  const m = MBY[id]; pick = {m:id, ad:m.h+' - '+m.a, lg:m.lg, k:m.k};
  setCanli(Date.now() >= Date.parse(m.k)); showLegForm();
}
function pickManual(){
  const ad = prompt('Maç adı (örn. Galatasaray - Fenerbahçe):'); if(!ad) return;
  pick = {m:null, ad:ad, lg:'Liste dışı', k:new Date().toISOString(), manual:true}; setCanli(false); showLegForm();
}
function setCanli(v){ canli = v; const a=$('b-on'), b=$('b-pre'); if(a){ a.classList.toggle('on',v); b.classList.toggle('on',!v); } }
function showLegForm(){
  $('legf').style.display = 'block';
  $('legt').innerHTML = '<b>'+esc(pick.ad)+'</b><small>'+esc(pick.lg)+(pick.manual?' · sonucu sen gireceksin':'')+'</small>';
  $('odd').value=''; setCanli(canli); $('odd').focus();
}
function addLeg(){
  const o = parseFloat(($('odd').value||'').replace(',','.'));
  if(!(o>1)) { msg('Oranı gir (örn. 1.76).'); return; }
  const b = $('mk').value;
  const mm = pick.m ? MBY[pick.m] : null, mp = (!canli && mm) ? modelP(b, mm.md) : null;
  draft.push(Object.assign({}, pick, {b:b, bl:MARKETS.find(x=>x[1]===b)[2], o:o, canli:canli, sonuc:null, mp: mp==null?null:Math.round(mp*1e4)/1e4}));
  $('legf').style.display='none'; pick=null; msg(''); renderDraft();
}
function renderDraft(){
  let o=1, mp=1, nm=0; draft.forEach(l=>{ o*=l.o; if(l.mp!=null) mp*=l.mp; else nm++; });
  $('draft').innerHTML = draft.map((l,i)=>{
    const imp = 1/l.o, low = l.mp!=null && l.mp < imp-0.05;
    const info = l.mp!=null ? ' · model <b>'+pc(l.mp)+'</b> · oranın varsaydığı '+pc(imp)+(low?' <span class="neg">⚠ model daha az emin</span>':'') : (l.canli?'':' · model verisi yok');
    return '<div class="leg"><div>'+esc(l.ad)+'<small>'+esc(l.bl)+' · '+(l.canli?'canlı':'maç öncesi')+info+'</small></div>'+
      '<div><b>'+l.o.toFixed(2)+'</b> <button class="btn sm" onclick="draft.splice('+i+',1);renderDraft()">×</button></div></div>'; }).join('');
  const t = parseFloat(($('stake').value||'').replace(',','.'))||0;
  let mtxt = '';
  if(draft.length && nm<draft.length){
    mtxt = '<div class="mp">Model: '+(nm?'model verisi olan '+(draft.length-nm)+' maçın':'tüm maçların')+' birlikte tutma ihtimali <b>'+pc(mp)+'</b>'+
           (mp>0?' (yaklaşık '+Math.max(1,Math.round(1/mp))+' kuponda 1)':'')+' · oranların varsaydığı '+pc(1/o)+'</div>';
  }
  $('tot').innerHTML = draft.length ? (draft.length+' maç · toplam oran <b>'+o.toFixed(2)+'</b>'+(t?' · olası kazanç <b>'+(t*o).toLocaleString('tr-TR',{maximumFractionDigits:2})+' TL</b>':'')+mtxt) : 'Kupon boş: yukarıdan maç seç.';
  $('savebox').style.display = draft.length ? 'block' : 'none';
}
async function saveCoupon(){
  const t = parseFloat(($('stake').value||'').replace(',','.'));
  if(!(t>0)){ msg('Kupon bedelini (TL) gir.'); return; }
  const kp = {id:'k'+Date.now(), t:new Date().toISOString(), tutar:t, legs:draft.map(l=>({m:l.m,ad:l.ad,lg:l.lg,k:l.k,b:l.b,bl:l.bl,o:l.o,canli:l.canli,sonuc:null,mp:l.mp}))};
  msg('Kaydediliyor…', true);
  try{ await ghSave(d=>d.kuponlar.push(kp), 'Kupon eklendi'); draft=[]; $('stake').value=''; renderDraft(); renderAll(); msg('Kupon kaydedildi ✓', true); }
  catch(e){ msg(esc(e.message)); }
}
async function delK(id){ if(!confirm('Bu kupon silinsin mi?')) return;
  try{ await ghSave(d=>{d.kuponlar=d.kuponlar.filter(k=>k.id!==id)}, 'Kupon silindi'); renderAll(); msg('Silindi', true);}catch(e){ msg(esc(e.message)); } }
async function setRes(id, i, v){
  try{ await ghSave(d=>{const k=d.kuponlar.find(k=>k.id===id); if(k) k.legs[i].sonuc=v;}, 'Sonuç girildi'); renderAll(); msg('Kaydedildi', true);}catch(e){ msg(esc(e.message)); } }
function renderCoupons(){
  const ks = DATA.kuponlar.slice().sort((a,b)=>(b.t||'').localeCompare(a.t||''));
  $('kps').innerHTML = ks.map(k=>{ const s=kState(k), t=+k.tutar||0;
    const mps = k.legs.map(l=>l.mp), kmp = mps.every(x=>x!=null) ? mps.reduce((a,b)=>a*b,1) : null;
    const lab = s.st==='tuttu'?'<span class="pos">Kazandı</span>':(s.st==='yatti'?'<span class="neg">Kaybetti</span>':'Bekliyor');
    return '<details class="kp"><summary><div class="kh"><span>'+dm(dayOf(k.t))+' '+hm(k.t)+' · '+k.legs.length+' maç · '+t.toLocaleString('tr-TR')+' TL × '+s.o.toFixed(2)+'</span><span>'+lab+'</span></div>'+
      '<div class="ks">'+esc(k.legs.map(l=>l.ad.split(' - ')[0]).slice(0,3).join(', '))+(k.legs.length>3?' …':'')+(kmp!=null?' · model '+pc(kmp):'')+'</div></summary>'+
      k.legs.map((l,i)=>{ const r=s.rs[i]; const m=l.m?MBY[l.m]:null;
        const mark = r===null ? ((l.m===null||l.b==='diger') ? '<button class="btn sm" onclick="setRes(\''+k.id+'\','+i+',\'tuttu\')">Tuttu</button> <button class="btn sm" onclick="setRes(\''+k.id+'\','+i+',\'yatti\')">Yattı</button>' : '⏳')
          : (r?'<span class="pos">✓</span>':'<span class="neg">✗</span>');
        return '<div class="leg"><div>'+esc(l.ad)+(m&&m.s?' <b>'+m.s[0]+'-'+m.s[1]+'</b>':'')+'<small>'+esc(l.bl)+' · '+(+l.o).toFixed(2)+(l.canli?' · canlı':'')+(l.mp!=null?' · model '+pc(l.mp):'')+'</small></div><div>'+mark+'</div></div>'; }).join('')+
      '<div style="text-align:right;margin-top:6px"><button class="btn sm" onclick="delK(\''+k.id+'\')">Sil</button></div></details>'; }).join('') ||
    '<p class="empty">Henüz kayıtlı kupon yok.</p>';
}
function renderAll(){ renderSummary(); renderCoupons(); }
function saveTok(){ try{ localStorage.setItem('nb_token', $('tk').value.trim()); }catch(e){} testTok(); }
async function testTok(){
  if(!tok()){ $('tks').textContent='Anahtar girilmedi: kupon kaydedemezsin.'; $('tks').style.color='var(--neg)'; return; }
  try{ const {data} = await ghLoad(); DATA = data; DATA.kuponlar = DATA.kuponlar||[]; renderAll();
    $('tks').textContent='Anahtar çalışıyor ✓'; $('tks').style.color='var(--ac)'; }
  catch(e){ $('tks').textContent=e.message; $('tks').style.color='var(--neg)'; }
}
async function init(){
  $('mk').innerHTML = mkSelect();
  try{ const r = await fetch('data/maclar.json?t='+Date.now()); const j = await r.json(); MACS=j.maclar||[]; DAILY=j.daily; FROM=j.from; }catch(e){ MACS=[]; }
  MACS.forEach(m=>MBY[m.id]=m);
  if(DAILY){ const y = dayOf(new Date(Date.now()-864e5).toISOString()); MACS = MACS.filter(m=>dayOf(m.k)>=y); }
  renderDays(); renderList(); renderDraft();
  if(tok()) await testTok();
  else { try{ const r = await fetch('data/bahislerim.json?t='+Date.now()); if(r.ok){ DATA=await r.json(); DATA.kuponlar=DATA.kuponlar||[]; } }catch(e){} renderAll(); testTok(); }
}
init();
"""


def write_bet_html():
    repo = json.dumps(os.environ.get("GITHUB_REPOSITORY", "") or "nattbot2302/nattbot")
    js = BET_JS.replace("__REPO__", repo).replace("__MARKETS__", json.dumps(BET_MARKETS, ensure_ascii=False))
    page = (f"<!doctype html><html lang='tr'><head><meta charset='utf-8'>"
            f"<meta name='viewport' content='width=device-width, initial-scale=1'>"
            f"<title>Kuponlarım</title><style>{CSS}{BET_CSS}</style></head><body>"
            "<header><div class='top'><h1>Kuponlarım</h1><a class='back' href='index.html'>← Günün maçları</a></div></header>"
            "<div class='wrapb'><div id='sum'></div>"
            "<div class='card'><h2>Yeni kupon</h2>"
            "<div class='row2'><select id='day' class='sel' onchange=\"$('q').value='';renderList()\"></select>"
            "<input id='q' class='in' placeholder='Takım ara' oninput='renderList()'></div>"
            "<div id='ml' class='mlist'></div>"
            "<div style='margin-top:8px'><button class='btn sm' onclick='pickManual()'>+ Listede olmayan maç</button></div>"
            "<div id='legf' class='legf' style='display:none'><div id='legt' class='leg' style='border:0'></div>"
            "<select id='mk' class='sel'></select>"
            "<div class='row2'><input id='odd' class='in' inputmode='decimal' placeholder='Oran (örn. 1.76)'></div>"
            "<div class='row2'><button id='b-pre' class='btn' onclick='setCanli(false)'>Maç öncesi</button>"
            "<button id='b-on' class='btn' onclick='setCanli(true)'>Canlı</button></div>"
            "<div class='row2'><button class='btn pri' onclick='addLeg()'>Kupona ekle</button>"
            "<button class='btn' onclick=\"$('legf').style.display='none'\">Vazgeç</button></div></div>"
            "<div class='sec'>Kupon</div><div id='draft'></div><div id='tot' class='tot'></div>"
            "<div id='savebox' style='display:none'><input id='stake' class='in' inputmode='decimal' placeholder='Kupon bedeli (TL)' oninput='renderDraft()'>"
            "<div class='row2'><button class='btn pri' onclick='saveCoupon()'>Kuponu kaydet</button></div></div>"
            "<div id='msg' class='msg'></div></div>"
            "<h2 style='margin-top:16px'>Kayıtlı kuponlar</h2><div id='kps'></div>"
            "<details class='rp' style='margin-top:14px'><summary><b>Ayarlar: GitHub anahtarı</b> <span id='tks' class='note'></span></summary>"
            "<div class='tc'>Kuponların repoya kaydedilmesi için bir kez anahtar girmen gerekir. Anahtar sadece bu "
            "telefonun tarayıcısında saklanır, sitede yayınlanmaz.<br>1. <a href='https://github.com/settings/personal-access-tokens/new' target='_blank'>"
            "Yeni anahtar oluştur</a> sayfasını aç.<br>2. Token name: <b>kupon</b>, Expiration: 1 yıl.<br>3. Repository access: "
            "<b>Only select repositories</b> → <b>nattbot</b>.<br>4. Permissions → Repository permissions → <b>Contents</b>: "
            "<b>Read and write</b>.<br>5. Generate token → kopyala → aşağıya yapıştır → Kaydet.</div>"
            "<input id='tk' class='in' type='password' placeholder='github_pat_...'>"
            "<div class='row2'><button class='btn pri' onclick='saveTok()'>Kaydet</button></div></details>"
            f"</div><script>{js}</script></body></html>")
    with open("bahis.html", "w", encoding="utf-8") as f:
        f.write(page)


def all_results(leagues):
    res = {}
    for L in leagues:
        res.update(L.get("results", {}))
    return res


def write_html(leagues, now, st=None):
    local = now.astimezone(TR)
    order = sorted(range(len(leagues)),
                   key=lambda i: (bool(leagues[i]["err"]), -len(leagues[i]["cards"]), i))
    nav = ["<option value='rapor' selected>Gol Raporu</option>", "<option value='t1'>T-1 · Dün ne oldu</option>",
           "<option value='ozet'>Özet</option>", "<option value='kupon'>Kuponlar</option>", "<optgroup label='Ligler'>"]
    st = st or {"preds": {}, "meta": {}}
    results = all_results(leagues)
    d0_, _ = day_window(now)
    today_cp = st.get("kupon", {}).get(f"{d0_:%Y-%m-%d}") or build_coupons(leagues, now)
    n_cp = [f"{short} {len(today_cp.get(k, []))}" for k, _, _, short in COUPONS if today_cp.get(k)]
    cp_banner = ("<div class='act' style='cursor:pointer' onclick=\"show('kupon')\"><b>Günün kuponları hazır →</b>"
                 f"<small>{' · '.join(n_cp)}</small></div>")
    tabs = [f"<section class='tab on' id='rapor'>{rapor_tab(leagues, now)}</section>",
            f"<section class='tab' id='ozet'>{cp_banner}{summary_tab(leagues)}</section>",
            f"<section class='tab' id='kupon'>{coupons_tab(st, today_cp, results, now)}</section>",
            f"<section class='tab' id='t1'>{learn_html(st, now)}{t1_tab(st, now)}</section>"]
    for i in order:
        L = leagues[i]
        tid = f"l{i}"
        nav.append(f"<option value='{tid}'>{E(L['name'])} ({len(L['cards'])} maç)</option>")
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
    nav.append("</optgroup><option value='bahis'>Bahislerim (kazanç analizi)</option><option value='karne'>Karne</option>")
    tabs.append(f"<section class='tab' id='bahis'>{bets_tab(st, MACS_BY_ID)}</section>")
    tabs.append(f"<section class='tab' id='karne'>{karne_tab(st, now)}{coupon_karne(st, results)}</section>")
    nav.append("<option value='dogruluk'>Doğruluk</option>")
    tabs.append(f"<section class='tab' id='dogruluk'>{accuracy_tab(leagues)}</section>")

    d0, d1 = day_window(now)
    page = (f"<!doctype html><html lang='tr'><head><meta charset='utf-8'>"
            f"<meta name='viewport' content='width=device-width, initial-scale=1'>"
            f"<title>Günün Maçları</title><style>{CSS}{RP_CSS}</style></head><body>"
            f"<header><div style='display:flex;justify-content:space-between;align-items:center'><h1>Günün Maçları</h1>"
            f"<span><a href='bahis.html?v={int(now.timestamp())}' style='background:var(--card);color:var(--tx);border:1px solid var(--bd);"
            f"text-decoration:none;font-weight:700;font-size:13px;padding:5px 11px;border-radius:16px;margin-right:6px'>Kuponlarım</a>"
            f"<a href='analiz.html?v={int(now.timestamp())}' style='background:var(--card);color:var(--tx);border:1px solid var(--bd);"
            f"text-decoration:none;font-weight:700;font-size:13px;padding:5px 11px;border-radius:16px;margin-right:6px'>Analiz</a>"
            f"<a href='canli.html?v={int(now.timestamp())}' style='background:#d93025;color:#fff;text-decoration:none;font-weight:700;"
            f"font-size:13px;padding:6px 12px;border-radius:16px'>● Canlı</a></span></div><div class='upd'>Güncelleme: {local:%d.%m.%Y %H:%M} · "
            f"Maçlar: {d0:%d.%m %H:%M} - {d1:%d.%m %H:%M} · Model tahmindir, kâr garantisi vermez."
            f"</div></header><div id='alarm' style='padding:0 12px'></div><nav><select id='navsel' onchange='show(this.value)'>{''.join(nav)}</select></nav>{''.join(tabs)}"
            f"<script>{JS}{RP_JS}</script><script>const REPO = {json.dumps(os.environ.get('GITHUB_REPOSITORY', ''))};"
            f"{live_core_js()}{ALARM_JS}</script></body></html>")
    with open("index.html", "w", encoding="utf-8") as f:
        f.write(page)


# -------------------------------------------------------------------- CANLI SAYFA
LIVE_MODEL = "data/canli_model.json"
LIVE_CTX = {"lg": {}, "tm": {}}
LIVE_TL_N = 40        # canlı analiz için takım başına son maç sayısı
LIVE_LG_N = 500       # canlı "benzer durum" için ligden son maç sayısı


def live_context(leagues, allpast):
    """Gol dakikalı maç zaman çizelgeleri: takım bazında (takımın gözünden) ve lig bazında (ev sahibinin gözünden).
    Gol dakikası verisi zayıf liglerde 0-0'lar tek başına kalıp sonucu çarpıtmasın diye o ligler hiç kullanılmaz."""
    tm, lg, seen, rows = defaultdict(list), {}, set(), []
    for L in leagues:
        if "_ctx" not in L:
            continue
        past = sorted(L["_ctx"][1], key=lambda m: m["date"])
        scored = [m for m in past if m["hg"] + m["ag"] > 0]
        cov = sum(1 for m in scored if m.get("gm")) / len(scored) if scored else 0
        if cov < 0.7:
            continue
        gl = [m["gm"] for m in past if m.get("gm") is not None][-LIVE_LG_N:]
        sts = [m["st"] for m in past[-LIVE_LG_N:] if m.get("st")]
        ok = len(sts) >= 30
        lg[L["slug"]] = {"g": gl,
                         "sh": round(sum(x["hs"] + x["as"] for x in sts) / len(sts), 2) if ok else None,
                         "sot": round(sum(x["hsot"] + x["asot"] for x in sts) / len(sts), 2) if ok else None}
        for m in past:
            if m.get("gm") is not None and m["id"] not in seen:
                seen.add(m["id"])
                rows.append(m)
    for m in sorted(rows, key=lambda m: m["date"]):
        g = m["gm"]
        d = f"{m['date'].astimezone(TR):%d.%m.%y}"
        tm[m["hid"]].append([d, 1, m["away"], m["hg"], m["ag"], g])
        tm[m["aid"]].append([d, 0, m["home"], m["ag"], m["hg"], [-x for x in g]])
    return {"lg": lg, "tm": tm}


def write_live_model(leagues, now):
    ms, lgs = [], {}
    for L in leagues:
        for c in L["cards"]:
            r = c["r"]
            if L["slug"] in LIVE_CTX["lg"]:
                lgs[L["slug"]] = LIVE_CTX["lg"][L["slug"]]
            ms.append({
                "tl": [LIVE_CTX["tm"].get(c.get("hid"), [])[-LIVE_TL_N:], LIVE_CTX["tm"].get(c.get("aid"), [])[-LIVE_TL_N:]],
                "id": c["id"], "slug": L["slug"], "lg": L["name"], "h": c["home"], "a": c["away"],
                "k": c["kick"].isoformat(),
                "lam": [round(x, 4) for x in c["lam"]],
                "lam1": [round(x, 4) for x in r["lam1"]] if r.get("lam1") else None,
                "pre": {k: round(r[k], 4) for k in ("p1", "px", "p2", "o15", "o25", "btts")},
            })
    os.makedirs(os.path.dirname(LIVE_MODEL), exist_ok=True)
    with open(LIVE_MODEL, "w", encoding="utf-8") as f:
        json.dump({"gen": now.isoformat(), "matches": ms, "lg": lgs}, f, ensure_ascii=False, separators=(",", ":"))


LIVE_CSS = """
.top{display:flex;justify-content:space-between;align-items:center;gap:8px}
.back{color:var(--ac);text-decoration:none;font-size:14px;font-weight:600}
.btn{border:1px solid var(--bd);background:var(--card);color:var(--tx);border-radius:16px;padding:7px 12px;font-size:13px}
.wrapc{padding:4px 12px 24px}
.live{display:inline-block;background:#d93025;color:#fff;font-size:11px;font-weight:700;padding:2px 7px;border-radius:6px;animation:bl 1.6s infinite}
@keyframes bl{50%{opacity:.55}}
.score{display:grid;grid-template-columns:1fr auto 1fr;align-items:center;gap:8px;margin:8px 0 4px}
.score .t{font-size:15px;font-weight:600}.score .t.r{text-align:right}
.score .s{font-size:30px;font-weight:800;letter-spacing:2px}
.rc{display:inline-block;width:9px;height:12px;background:#d93025;border-radius:2px;margin:0 2px;vertical-align:-1px}
.bar{display:flex;height:8px;border-radius:4px;overflow:hidden;background:var(--lo);margin:3px 0 8px}
.bar i{display:block;height:100%}
.bh{background:var(--ac)}.ba{background:var(--warn)}
.st{display:grid;grid-template-columns:36px 1fr 36px;font-size:12.5px;align-items:center;color:var(--mu)}
.st b{color:var(--tx)}.st span:last-child{text-align:right}
.act{border-left:3px solid var(--ac);padding:6px 10px;margin:6px 0;background:var(--lo);border-radius:0 8px 8px 0;font-size:13.5px}
.act small{display:block;color:var(--mu);font-size:11.5px;margin-top:2px}
.ng{display:flex;height:22px;border-radius:6px;overflow:hidden;font-size:11px;font-weight:700;color:#fff;margin-top:6px}
.ng div{display:flex;align-items:center;justify-content:center;min-width:0;overflow:hidden;white-space:nowrap}
.ban{border:1px solid var(--warn);color:var(--warn);border-radius:10px;padding:10px;font-size:13px;margin:8px 0}
.pk{border-left:3px solid var(--ac);background:var(--lo);border-radius:0 8px 8px 0;padding:6px 10px;margin:6px 0;font-size:13.5px}
.pk summary{cursor:pointer}
.ck{font-size:12.5px;margin:4px 0 0 2px}.ck.y{color:var(--tx)}.ck.n{color:var(--mu)}
.lvl{display:inline-block;font-size:10.5px;font-weight:800;padding:1px 6px;border-radius:5px;color:#fff}
.lvl.g{background:#1e8e3e}.lvl.o{background:#e37400}
.rx{font-size:13px;margin:6px 0;line-height:1.45}
.rx details summary{font-size:12px;color:var(--ac);cursor:pointer}
.vt{font-size:12px;font-weight:700;color:var(--mu);margin:8px 0 2px;text-transform:uppercase;letter-spacing:.3px}
.pk.iy{border-left-color:#8e44ad}
.iyt{color:#b07cc6}
"""

LIVE_JS = r"""
const MODEL_URL = 'data/canli_model.json';
let MODEL = null;
let DIRECT = true;               // tarayıcı ESPN'e doğrudan bağlanabiliyor mu
let SOURCE = '';
function repoSlug(){
  if(REPO) return REPO;
  const owner = location.hostname.split('.')[0], name = location.pathname.split('/').filter(Boolean)[0];
  return owner+'/'+name;
}
async function fetchRelay(){
  const api = 'https://api.github.com/repos/'+repoSlug()+'/contents/canli.json?ref=canli';
  let j = null;
  try{
    const r = await fetch(api, {headers:{'Accept':'application/vnd.github.raw+json'}, cache:'no-store'});
    if(r.ok) j = await r.json();
    else if(r.status===404) throw new Error('aktarım henüz başlamadı');
  }catch(e){ if(String(e.message).includes('başlamadı')) throw e; }
  if(!j){
    const r = await fetch('https://raw.githubusercontent.com/'+repoSlug()+'/canli/canli.json?t='+Date.now());
    if(!r.ok) throw new Error('aktarım verisi yok');
    j = await r.json();
  }
  return j;
}
const SOT_GOAL = 0.32;          // isabetli şut başına ortalama gol
const RED_OWN = 0.70, RED_OPP = 1.25;
function esc(s){return String(s).replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));}
function pct(x){return x==null||isNaN(x)?'-':Math.round(x*100)+'%';}
function fair(p){return p>0.005?(1/p).toFixed(2):'-';}
function cls(p){p=Math.round(p*100)/100;return p>=0.6?'hi':(p>=0.45?'mid':'lo');}
function pois(k,l){let p=Math.exp(-l);for(let i=1;i<=k;i++)p*=l/i;return p;}
function dist(l,n){n=n||11;const a=[];for(let k=0;k<n;k++)a.push(pois(k,l));const s=a.reduce((x,y)=>x+y,0);return a.map(x=>x/s);}
function ymd(d){return d.toISOString().slice(0,10).replace(/-/g,'');}
function hm(d){return d.toLocaleTimeString('tr-TR',{hour:'2-digit',minute:'2-digit',timeZone:'Europe/Istanbul'});}

async function loadModel(){
  const r = await fetch(MODEL_URL+'?t='+Date.now());
  if(!r.ok) throw new Error('model dosyası yok');
  MODEL = await r.json();
}

async function fetchEvents(slug, dates){
  const out = {};
  for(const d of dates){
    const r = await fetch('https://site.api.espn.com/apis/site/v2/sports/soccer/'+slug+'/scoreboard?dates='+d);
    if(!r.ok) throw new Error('HTTP '+r.status);
    const j = await r.json();
    for(const ev of (j.events||[])) out[ev.id] = ev;
  }
  return out;
}

function parseLive(ev){
  const c = ev.competitions[0], st = ev.status||{}, ty = st.type||{};
  let h=null, a=null;
  for(const x of c.competitors){ if(x.homeAway==='home') h=x; else a=x; }
  const stat = (x,n)=>{const s=(x.statistics||[]).find(s=>s.name===n); const v=s?parseFloat(s.displayValue):NaN; return isNaN(v)?null:v;};
  const pick = x=>({pos:stat(x,'possessionPct'), sh:stat(x,'totalShots'), sot:stat(x,'shotsOnTarget'), cor:stat(x,'wonCorners')});
  const hid = String(h.team.id), aid = String(a.team.id);
  const red = [0,0];
  for(const d of (c.details||[])){
    if(!d.redCard || !d.team) continue;
    const t = String(d.team.id);
    if(t===hid) red[0]++; else if(t===aid) red[1]++;
  }
  return {state:ty.state, name:ty.name||'', detail:ty.shortDetail||ty.detail||'', done:!!ty.completed,
          min:(st.clock||0)/60, period:st.period||0, disp:st.displayClock||'',
          hg:parseInt(h.score||0)||0, ag:parseInt(a.score||0)||0, stats:{h:pick(h), a:pick(a)}, red:red, hist:ev.hist||null};
}

// Kalan sürede beklenen gol: maç öncesi model + kırmızı kart + isabetli şut ayarı
function remaining(m, L){
  const lam = m.lam, l1 = m.lam1 || [lam[0]*0.45, lam[1]*0.45];
  const l2 = [Math.max(lam[0]-l1[0],0.05), Math.max(lam[1]-l1[1],0.05)];
  const ht = L.name==='STATUS_HALFTIME' || L.detail==='HT';
  let rem, rem1 = null;
  if(ht){ rem = l2.slice(); }
  else if(L.period<=1){
    const f = Math.max(47-L.min, 0.5)/47;
    rem1 = [l1[0]*f, l1[1]*f];
    rem = [rem1[0]+l2[0], rem1[1]+l2[1]];
  } else {
    const f = Math.max(50-(L.min-45), 0.5)/50;
    rem = [l2[0]*f, l2[1]*f];
  }
  const notes = [];
  // kırmızı kart
  for(let i=0;i<2;i++){
    const k = Math.pow(RED_OWN, L.red[i]) * Math.pow(RED_OPP, L.red[1-i]);
    rem[i] *= k; if(rem1) rem1[i] *= k;
  }
  if(L.red[0]||L.red[1]) notes.push('Kırmızı kart hesaba katıldı: eksik kalan takımın gol beklentisi düşürüldü, rakibinki artırıldı.');
  // maç istatistiği: isabetli şut temposu
  const tp = Math.min(L.min, 95);
  const press = [1, 1];
  const sot = [L.stats.h.sot, L.stats.a.sot];
  if(tp>=15 && sot[0]!=null && sot[1]!=null){
    const w = Math.min(0.4, tp/90*0.45);
    for(let i=0;i<2;i++){
      const prior = lam[i]/97, obs = SOT_GOAL*sot[i]/tp;
      let f = ((1-w)*prior + w*obs)/prior;
      f = Math.min(1.6, Math.max(0.6, f));
      press[i] = f;
      rem[i] *= f; if(rem1) rem1[i] *= f;
      if(f>=1.15) notes.push((i?m.a:m.h)+' beklenenden fazla isabetli şut çekiyor ('+sot[i]+'): kalan gol beklentisi %'+Math.round((f-1)*100)+' artırıldı.');
      if(f<=0.85) notes.push((i?m.a:m.h)+' beklenenden az isabetli şut çekiyor ('+sot[i]+'): kalan gol beklentisi %'+Math.round((1-f)*100)+' azaltıldı.');
    }
  }
  return {rem, rem1, ht, notes, press};
}

// ---- Canlı analiz: dakika, benzer durumlar, takım tepkisi, tempo (ilk yarı ve maç sonu ayrı)
function tNow(L){
  if(L.name==='STATUS_HALFTIME'||L.detail==='HT') return 45;
  return Math.round(L.period<=1 ? Math.min(Math.max(L.min,1),45) : Math.max(L.min,46));
}
function stAt(g,t){let h=0,a=0;for(const x of g){if(Math.abs(x)<=t){if(x>0)h++;else a++;}}return [h,a];}
// t'den sonra, end dakikasına kadar (ilk yarı için 45: uzatma golleri 45 sayılır)
function aft(g,t,end){end=end||999;let h=0,a=0,first=null,fs=0;for(const x of g){const mn=Math.abs(x);if(mn>t&&mn<=end){if(x>0)h++;else a++;if(first===null||mn<first){first=mn;fs=x>0?1:-1;}}}return {h,a,n:h+a,first,fs};}
function frac(arr,f){if(!arr.length)return null;let k=0;for(const x of arr)if(f(x))k++;return k/arr.length;}
function mean(arr,f){if(!arr.length)return null;let s=0;for(const x of arr)s+=f(x);return s/arr.length;}
function P(x){return x==null?'-':'%'+Math.round(x*100);}
function leadTxt(d){return d>0?d+' farkla öndeyken':(d<0?(-d)+' farkla gerideyken':'berabereyken');}
function pAtLeast(l,k){let c=0;for(let i=0;i<k;i++)c+=pois(i,l);return Math.max(0,1-c);}

// Ligde bu dakikada aynı skor / aynı farkta olan maçlarda sonrası (end dakikasına kadar) ne oldu
function lgSimilar(m, L, t, end){
  const G = MODEL.lg && MODEL.lg[m.slug]; if(!G || !G.g || G.g.length<40) return null;
  const d = L.hg-L.ag;
  const tiers = [['aynı skor ('+L.hg+'-'+L.ag+')', s=>s[0]===L.hg&&s[1]===L.ag], ['aynı fark ('+(d===0?'beraberlik':(d>0?'ev sahibi '+d+' önde':'deplasman '+(-d)+' önde'))+')', s=>s[0]-s[1]===d], ['bu dakikadaki tüm maçlar', s=>true]];
  const all = G.g.map(g=>({s:stAt(g,t), a:aft(g,t,end)}));
  for(let i=0;i<tiers.length;i++){
    const rows = all.filter(r=>tiers[i][1](r.s));
    if(rows.length>=25 || i===tiers.length-1){
      const n = rows.length; if(!n) return null;
      const o = {lab:tiers[i][0], n, tier:i,
        more1:frac(rows,r=>r.a.n>=1), more2:frac(rows,r=>r.a.n>=2), mean:mean(rows,r=>r.a.n),
        nextH:frac(rows,r=>r.a.fs===1), nextA:frac(rows,r=>r.a.fs===-1),
        scH:frac(rows,r=>r.a.h>=1), scA:frac(rows,r=>r.a.a>=1),
        in15:frac(rows,r=>r.a.first!==null&&r.a.first<=t+15), in30:frac(rows,r=>r.a.first!==null&&r.a.first<=t+30)};
      if(i<2){
        if(d!==0) o.leadWin = frac(rows,r=>{const fh=r.s[0]+r.a.h, fa=r.s[1]+r.a.a; return d>0?fh>fa:fa>fh;});
        else o.keepDraw = frac(rows,r=>r.s[0]+r.a.h===r.s[1]+r.a.a);
      }
      return o;
    }
  }
  return null;
}

// Takımın kendi geçmişi: bu dakikada aynı durumdayken ne yaptı? (end: 45 ise devreye kadar)
function teamReact(rows, d, t, end){
  if(!rows || !rows.length) return null;
  const iy = end && end<=45;
  const fin = r => iy ? stAt(r[5],45) : [r[3],r[4]];
  const all = rows.map(r=>({r, s:stAt(r[5],t), a:aft(r[5],t,end), f:fin(r)}));
  let lab = t+'. dk '+leadTxt(d), sel = all.filter(x=>x.s[0]-x.s[1]===d), relaxed = false;
  if(sel.length<3 && d!==0){
    const sg = Math.sign(d), alt = all.filter(x=>Math.sign(x.s[0]-x.s[1])===sg);
    if(alt.length>sel.length){ sel = alt; relaxed = true; lab = t+'. dk '+(d>0?'öndeyken':'gerideyken')+' (fark ne olursa olsun)'; }
  }
  let tot=0, late=0;
  for(const x of all) for(const g of x.r[5]) if(g>0){ tot++; if(g>t && g<=(end||999)) late++; }
  const gen = {n:all.length, any:frac(all,x=>x.a.n>=1), mean:mean(all,x=>x.a.n), gf:mean(all,x=>x.a.h), ga:mean(all,x=>x.a.a), share: tot? late/tot : null};
  const o = {lab, n:sel.length, relaxed, gen, iy};
  if(sel.length){
    o.scored = frac(sel,x=>x.a.h>=1); o.conceded = frac(sel,x=>x.a.a>=1);
    o.gf = mean(sel,x=>x.a.h); o.ga = mean(sel,x=>x.a.a);
    o.win = frac(sel,x=>x.f[0]>x.f[1]); o.draw = frac(sel,x=>x.f[0]===x.f[1]);
    o.list = sel.slice(-6).reverse().map(x=>({d:x.r[0], home:x.r[1], opp:x.r[2], at:x.s, ht:stAt(x.r[5],45), fin:[x.r[3],x.r[4]], gf:x.a.h, ga:x.a.a}));
  }
  return o;
}

// Maçın temposu: şimdiye kadarki ve son ~15 dakikadaki şut sayısı, lig ortalamasına göre
function tempo(m, L, t){
  const G = MODEL.lg && MODEL.lg[m.slug], s = L.stats;
  if(s.h.sh==null || s.a.sh==null || t<10) return null;
  const base = (G && G.sh) || 24;
  const sh = s.h.sh+s.a.sh, exp = base*t/93;
  const o = {sh, sot:(s.h.sot||0)+(s.a.sot||0), exp, base, ratio: sh/Math.max(exp,1)};
  const H = L.hist;
  if(H && H.length>=2){
    const last = H[H.length-1]; let ref = null;
    for(let i=H.length-2;i>=0;i--){ if(last[0]-H[i][0]>=10){ ref = H[i]; break; } }
    if(ref){
      const span = last[0]-ref[0], v = (r,i)=>r[i]||0;
      const dsh = v(last,1)+v(last,2)-v(ref,1)-v(ref,2);
      o.recent = {span:Math.round(span), sh:dsh, sot:v(last,3)+v(last,4)-v(ref,3)-v(ref,4),
                  shH:v(last,1)-v(ref,1), shA:v(last,2)-v(ref,2), ratio: dsh/Math.max(base*span/93,0.5)};
    }
  }
  o.r = o.recent ? 0.6*o.recent.ratio+0.4*o.ratio : o.ratio;
  o.lab = o.r>=1.25 ? 'yüksek' : (o.r<=0.8 ? 'düşük' : 'normal');
  return o;
}

// Bir zaman dilimi için (maç sonu: end=999, ilk yarı: end=45) kanıtların birleşimi
function scopeEval(m, L, t, end, rem){
  const d = L.hg-L.ag, lamM = Math.max(rem[0]+rem[1], 1e-6);
  const S = lgSimilar(m, L, t, end);
  const tl = m.tl || [[],[]];
  const TM = [teamReact(tl[0], d, t, end), teamReact(tl[1], -d, t, end)];
  const T = tempo(m, L, t);
  const k = T ? Math.min(1.2, Math.max(0.85, Math.pow(T.r, 0.3))) : 1;   // geçmiş veriler tempoyu bilmez
  let num = lamM, den = 1;
  if(S){ const w = Math.min(1, S.n/(S.n+40)); num += w*S.mean*k; den += w; }
  const g0 = TM[0]&&TM[0].gen, g1 = TM[1]&&TM[1].gen;
  if(g0 && g1 && g0.n>=5 && g1.n>=5){ const w = Math.min(g0.n,g1.n)/(Math.min(g0.n,g1.n)+25); num += w*(g0.mean+g1.mean)/2*k; den += w; }
  const lam = Math.max(num/den, 0.005);
  let sh = rem[0]/lamM;
  if(S && S.nextH+S.nextA>0.15) sh = 0.65*sh + 0.35*S.nextH/(S.nextH+S.nextA);
  const lh = lam*sh, la = lam*(1-sh);
  const o = {end, iy:end<=45, t, rem, S, TM, T, lam, lamM, lh, la, more1:1-Math.exp(-lam), more2:pAtLeast(lam,2), p1:0, px:0, p2:0, scores:{}};
  const dh = dist(lh), da = dist(la);
  for(let i=0;i<dh.length;i++) for(let j=0;j<da.length;j++){
    const p = dh[i]*da[j], fh = L.hg+i, fa = L.ag+j;
    if(fh>fa) o.p1+=p; else if(fh===fa) o.px+=p; else o.p2+=p;
    const kk = fh+'-'+fa; o.scores[kk] = (o.scores[kk]||0)+p;
  }
  o.nextH = o.more1*sh; o.nextA = o.more1*(1-sh);
  return o;
}

function liveEval(m, L){
  const t = tNow(L), R = remaining(m, L);
  const ft = scopeEval(m, L, t, 999, R.rem);
  const iy = (R.rem1 && !R.ht && L.period<=1) ? scopeEval(m, L, t, 45, R.rem1) : null;
  const o = Object.assign({}, ft, {R, ht:R.ht, ft, iy});
  o.picks = livePicks(m, L, ft);
  o.iyPicks = iy ? livePicks(m, L, iy) : [];
  return o;
}

function ck(lab, ok, txt){ return {lab, ok, txt}; }
function livePicks(m, L, o){
  const cur = L.hg+L.ag, t = o.t, S = o.S, T = o.T, d = L.hg-L.ag, TM = o.TM, nm = [m.h, m.a], iy = o.iy;
  const pre = iy ? 'İY ' : '', when = iy ? 'devreye kadar ' : 'maç sonuna kadar ';
  const pm1 = 1-Math.exp(-o.lamM), pm2 = pAtLeast(o.lamM, 2);
  const tr = d===0 ? null : (d>0 ? 1 : 0), ld = d===0 ? null : 1-tr;
  const ok3 = i => TM[i] && TM[i].n>=3;
  const genAny = (TM[0]&&TM[1]&&TM[0].gen.n>=5&&TM[1].gen.n>=5) ? (TM[0].gen.any+TM[1].gen.any)/2 : null;
  const span = iy ? t+'. dakika ile devre arası' : t+'. dakikadan sonra';
  const out = [];
  { // bir gol daha
    const c = [ck('Model', pm1>=0.6, when+'gol ihtimali '+P(pm1))];
    if(S) c.push(ck('Ligde benzer maçlar', S.more1>=0.6, S.lab+': '+S.n+' maçta '+when+'gol olma oranı '+P(S.more1)));
    if(genAny!=null) c.push(ck('İki takımın maçları', genAny>=0.6, span+' gol olan maç oranı '+P(genAny)));
    if(T) c.push(ck('Tempo', T.r>=1, 'tempo '+T.lab));
    if(tr!=null && ok3(tr)) c.push(ck(nm[tr]+' tepkisi', TM[tr].scored>=0.5, TM[tr].lab+' '+TM[tr].n+' maçta '+when+'gol atma oranı '+P(TM[tr].scored)));
    out.push({t:pre+(cur+0.5)+' Üst', sub:iy?'ilk yarıda bir gol daha':'bir gol daha', p:o.more1, c});
  }
  { // iki gol daha
    const c = [ck('Model', pm2>=0.55, when+'iki gol daha ihtimali '+P(pm2))];
    if(S) c.push(ck('Ligde benzer maçlar', S.more2>=0.55, S.n+' maçta '+when+'2+ gol oranı '+P(S.more2)));
    if(T) c.push(ck('Tempo', T.r>=1.15, 'tempo '+T.lab));
    out.push({t:pre+(cur+1.5)+' Üst', sub:iy?'ilk yarıda iki gol daha':'iki gol daha', p:o.more2, c});
  }
  if(t >= (iy ? 20 : 55)){ // bu skorla biter
    const c = [ck('Model', pm1<=0.4, when+'gol olmama ihtimali '+P(1-pm1))];
    if(S) c.push(ck('Ligde benzer maçlar', S.more1<=0.4, S.lab+': '+S.n+' maçta '+when+'golsüz geçme oranı '+P(1-S.more1)));
    if(genAny!=null) c.push(ck('İki takımın maçları', genAny<=0.45, span+' golsüz geçen maç oranı '+P(1-genAny)));
    if(T) c.push(ck('Tempo', T.r<=0.9, 'tempo '+T.lab));
    if(tr!=null && ok3(tr)) c.push(ck(nm[tr]+' tepkisi', TM[tr].scored<0.35, TM[tr].lab+' '+TM[tr].n+' maçta '+when+'gol atma oranı sadece '+P(TM[tr].scored)));
    out.push({t:pre+(cur+0.5)+' Alt', sub:iy?'ilk yarı bu skorla biter':'bu skorla biter', p:1-o.more1, c});
  }
  if(!iy){
    for(const i of [0,1]){ // sıradaki gol
      const p = i ? o.nextA : o.nextH, shm = o.rem[i]/o.lamM;
      const c = [ck('Model', shm*pm1>=0.45, 'sıradaki golde bu takımın payı '+P(shm))];
      if(S) c.push(ck('Ligde benzer maçlar', (i?S.nextA:S.nextH)>=0.45, 'sıradaki golü bu tarafın atma oranı '+P(i?S.nextA:S.nextH)));
      if(ok3(i)) c.push(ck(nm[i]+' tepkisi', TM[i].scored>=0.5 && TM[i].gf>=TM[i].ga, TM[i].lab+' maç başı '+TM[i].gf.toFixed(1)+' attı, '+TM[i].ga.toFixed(1)+' yedi'));
      const so = [L.stats.h.sot, L.stats.a.sot];
      if(so[0]!=null && so[1]!=null) c.push(ck('Baskı', so[i]>so[1-i], 'isabetli şut '+so[i]+'-'+so[1-i]));
      out.push({t:'Sıradaki gol: '+nm[i], sub:'', p, c});
    }
    if(!(L.hg>0&&L.ag>0) && cur>0){ // KG Var
      const z = L.hg===0 ? 0 : 1, pz = 1-Math.exp(-(z?o.la:o.lh)), pmz = 1-Math.exp(-o.rem[z]);
      const c = [ck('Model', pmz>=0.55, nm[z]+' için gol ihtimali '+P(pmz))];
      if(S) c.push(ck('Ligde benzer maçlar', (z?S.scA:S.scH)>=0.5, 'bu tarafın gol attığı maç oranı '+P(z?S.scA:S.scH)));
      if(ok3(z)) c.push(ck(nm[z]+' tepkisi', TM[z].scored>=0.55, TM[z].lab+' gol atma oranı '+P(TM[z].scored)));
      out.push({t:'KG Var', sub:nm[z]+' de gol atar', p:pz, c});
    }
  }
  if(d!==0 && t >= (iy ? 20 : 30)){ // önde olan kazanır / devreyi önde kapatır
    const p = d>0 ? o.p1 : o.p2, w = iy ? 'devreyi önde kapatma' : 'kazanma';
    const c = [ck('Model', p>=0.7, w+' ihtimali '+P(p))];
    if(S && S.leadWin!=null) c.push(ck('Ligde benzer maçlar', S.leadWin>=0.7, S.n+' maçta önde olanın '+w+' oranı '+P(S.leadWin)));
    if(ok3(ld)) c.push(ck(nm[ld]+' tepkisi', TM[ld].win>=0.7, TM[ld].lab+' '+w+' oranı '+P(TM[ld].win)));
    if(ok3(tr)) c.push(ck(nm[tr]+' tepkisi', TM[tr].win+TM[tr].draw<=0.3, TM[tr].lab+' '+(iy?'devreyi geride kapatmama':'puan alma')+' oranı '+P(TM[tr].win+TM[tr].draw)));
    out.push({t:(iy?'İY ':'MS ')+(d>0?'1':'2'), sub:nm[ld]+(iy?' devreyi önde kapatır':' kazanır'), p, c});
  }
  if(d===0 && iy && t>=25){ // ilk yarı berabere biter
    const c = [ck('Model', o.px>=0.65, 'devrenin berabere bitme ihtimali '+P(o.px))];
    if(S && S.keepDraw!=null) c.push(ck('Ligde benzer maçlar', S.keepDraw>=0.65, S.n+' maçta devrenin berabere bitme oranı '+P(S.keepDraw)));
    for(const i of [0,1]) if(ok3(i)) c.push(ck(nm[i]+' tepkisi', TM[i].draw>=0.6, TM[i].lab+' devrenin berabere bitme oranı '+P(TM[i].draw)));
    out.push({t:'İY X', sub:'ilk yarı berabere biter', p:o.px, c});
  }
  for(const x of out){
    const v = x.c.filter(y=>y.ok!=null);
    x.ok = v.filter(y=>y.ok).length; x.n = v.length; x.ratio = x.n ? x.ok/x.n : 0;
    x.level = (x.c[0].ok && x.p>=0.65 && x.ratio>=0.8 && x.n>=3) ? 'Güçlü' : ((x.c[0].ok && x.p>=0.58 && x.ratio>=0.6 && x.n>=2) ? 'Orta' : null);
    x.iy = iy;
  }
  return out.filter(x=>x.p<=0.93).sort((a,b)=>(b.level==='Güçlü')-(a.level==='Güçlü') || (!!b.level)-(!!a.level) || b.ratio-a.ratio || b.p-a.p);
}

async function getLiveData(){
  if(!MODEL) await loadModel();
  const now = Date.now();
  const relevant = MODEL.matches.filter(m=>{const k=Date.parse(m.k); return k-now < 3*3600e3 && now-k < 3*3600e3;});
  const bySlug = {};
  for(const m of relevant){
    if(Date.parse(m.k) - now > 45*60e3) continue;
    const k = new Date(Date.parse(m.k));
    (bySlug[m.slug] = bySlug[m.slug] || new Set()).add(ymd(k)).add(ymd(new Date(k.getTime()-864e5)));
  }
  let evs = {}; let err = null, relayAge = null;
  if(DIRECT && Object.keys(bySlug).length){
    await Promise.all(Object.entries(bySlug).map(async ([slug, ds])=>{
      try{ Object.assign(evs, await fetchEvents(slug, [...ds])); }catch(e){ err = e; }
    }));
    if(err && !Object.keys(evs).length){ DIRECT = false; err = null; }
    else SOURCE = 'ESPN (doğrudan)';
  }
  if(!DIRECT && Object.keys(bySlug).length){
    try{
      const j = await fetchRelay();
      evs = j.events || {};
      relayAge = (now - Date.parse(j.t))/60000;
      SOURCE = 'bot aktarımı · '+(relayAge<1?'az önce':Math.round(relayAge)+' dk önce');
    }catch(e){ err = e; }
  }
  return {relevant, evs, err, relayAge, now};
}

// Canlı alarm: kanıtları birbirini tutan bir canlı bahis (ilk yarı ya da maç sonu) çıktığında
function alarmScan(m, L){
  const o = liveEval(m, L);
  const best = o.iyPicks.concat(o.picks).filter(x=>x.level).sort((a,b)=>(b.level==='Güçlü')-(a.level==='Güçlü') || b.ratio-a.ratio || b.p-a.p)[0];
  if(!best) return null;
  const reasons = [];
  if(best.iy) reasons.push('İlk yarı');
  if(o.T && o.T.lab!=='normal') reasons.push('Tempo '+o.T.lab);
  if(L.red[0]||L.red[1]) reasons.push('Kırmızı kart ('+(L.red[0]?m.h:m.a)+')');
  reasons.push(best.ok+'/'+best.n+' kanıt');
  const level = best.level==='Güçlü' ? 'kritik' : 'takip';
  return {m, L, o, bet:best, reasons, level, score: best.p + (best.level==='Güçlü'?0.5:0) + best.ratio*0.2};
}

function box(label,p){return '<div class="b '+cls(p)+'">'+esc(label)+'<br><b>'+pct(p)+'</b></div>';}

function statRow(label, h, a, suffix){
  if(h==null||a==null) return '';
  const t = (h+a)||1;
  return '<div class="st"><span><b>'+h+(suffix||'')+'</b></span><span style="text-align:center">'+label+'</span><span><b>'+a+(suffix||'')+'</b></span></div>'+
         '<div class="bar"><i class="bh" style="width:'+(h/t*100)+'%"></i><i class="ba" style="width:'+(a/t*100)+'%"></i></div>';
}

function pickHtml(x){
  const lv = x.level ? '<span class="lvl '+(x.level==='Güçlü'?'g':'o')+'">'+x.level.toUpperCase()+'</span> ' : '';
  return '<details class="pk'+(x.iy?' iy':'')+'"><summary>'+lv+'<b>'+esc(x.t)+'</b>'+(x.sub?' <span class="note">'+esc(x.sub)+'</span>':'')+
    ' · <b>'+P(x.p)+'</b> <span class="note">· '+x.ok+'/'+x.n+' kanıt</span></summary>'+
    x.c.map(y=>'<div class="ck '+(y.ok?'y':'n')+'">'+(y.ok?'✓':'✗')+' <b>'+esc(y.lab)+':</b> '+esc(y.txt)+'</div>').join('')+'</details>';
}

function verdict(picks, title){
  const strong = picks.filter(x=>x.level);
  let h = '<div class="vt">'+title+'</div>';
  if(strong.length) return h + strong.slice(0,2).map(pickHtml).join('');
  const b = picks.slice().sort((a,c)=>c.ratio-a.ratio||c.p-a.p)[0];
  return h + '<div class="ban">Net sinyal yok: kanıtlar birbirini tutmuyor.'+(b?' En yakın: <b>'+esc(b.t)+'</b> '+P(b.p)+' ('+b.ok+'/'+b.n+' kanıt).':'')+'</div>';
}

function reactHtml(nm, x, y){
  if(!x) return '<p class="note">'+esc(nm)+': gol dakikası olan geçmiş maç yok.</p>';
  let h = '<div class="rx"><b>'+esc(nm)+'</b> · ';
  if(!x.n) h += esc(x.lab)+' durumunda geçmiş maç bulunamadı ('+x.gen.n+' maç tarandı).';
  else {
    h += esc(x.lab)+': <b>'+x.n+' maç</b>. Sonrasında gol attığı maç '+P(x.scored)+', gol yediği maç '+P(x.conceded)+
         ' (maç başı '+x.gf.toFixed(1)+' attı, '+x.ga.toFixed(1)+' yedi). Maç sonu: galibiyet '+P(x.win)+', beraberlik '+P(x.draw)+', mağlubiyet '+P(1-x.win-x.draw)+'.';
    if(y && y.n) h += ' <span class="iyt">Devreye kadar: gol attığı maç '+P(y.scored)+', yediği '+P(y.conceded)+'; devreyi önde kapattığı '+P(y.win)+'.</span>';
    h += '<details><summary>Maçlar</summary>'+x.list.map(r=>'<div class="note">'+esc(r.d)+' · '+(r.home?'ev':'dep')+' · '+esc(r.opp)+
         ' · o dakikada <b>'+r.at[0]+'-'+r.at[1]+'</b> → devre '+r.ht[0]+'-'+r.ht[1]+' → maç sonu <b>'+r.fin[0]+'-'+r.fin[1]+'</b>'+
         ' (sonrası '+r.gf+'-'+r.ga+')</div>').join('')+'</details>';
  }
  return h+'</div>';
}

function liveCard(m, L){
  const o = liveEval(m, L), iy = o.iy;
  const reds = n=>Array(n).fill('<span class="rc"></span>').join('');
  const minute = o.ht ? 'Devre arası' : (L.disp||'');
  let out = '<div class="card" id="m'+m.id+'"><div class="meta"><span class="live">CANLI</span> '+esc(minute)+' · '+esc(m.lg)+'</div>';
  out += '<div class="score"><div class="t">'+esc(m.h)+' '+reds(L.red[0])+'</div><div class="s">'+L.hg+' - '+L.ag+'</div><div class="t r">'+reds(L.red[1])+' '+esc(m.a)+'</div></div>';

  // 1) Ne oynanır: ilk yarı ve maç sonu ayrı
  out += '<div class="sec">Ne oynanır?</div>';
  if(iy) out += verdict(o.iyPicks, 'İlk yarı · devreye ~'+Math.max(45-o.t,1)+' dk');
  else out += '<div class="vt">İlk yarı</div><p class="note">'+(o.ht?'Devre arası':'İlk yarı bitti')+'; ilk yarı bahisleri kapandı.</p>';
  out += verdict(o.picks, 'Maç sonu');
  out += '<details><summary>Tüm seçenekler ve kanıtları</summary>'+
         (iy ? '<div class="vt">İlk yarı</div>'+o.iyPicks.map(pickHtml).join('') : '')+
         '<div class="vt">Maç sonu</div>'+o.picks.map(pickHtml).join('')+'</details>';

  // 2) Tempo
  const T = o.T;
  out += '<div class="sec">Tempo</div>';
  if(T){
    out += '<div class="row">Maçta <b>'+T.sh+' şut</b> ('+T.sot+' isabetli). Ligde bu dakikaya kadar ortalama '+T.exp.toFixed(0)+' şut atılıyor → tempo <b>'+T.lab+'</b>.</div>';
    if(T.recent) out += '<div class="row">Son '+T.recent.span+' dakika: <b>'+T.recent.sh+' şut</b> ('+esc(m.h)+' '+T.recent.shH+', '+esc(m.a)+' '+T.recent.shA+'), '+T.recent.sot+' isabetli.</div>';
  } else out += '<p class="note">Şut verisi henüz yok.</p>';
  for(const n of o.R.notes) out += '<p class="note">'+esc(n)+'</p>';

  // 3) Ligde benzer durumlar
  const S = o.S;
  out += '<div class="sec">Ligde '+o.t+'. dakikada benzer durumdaki maçlar</div>';
  if(S){
    if(iy && iy.S) out += '<div class="row iyt">Devreye kadar ('+esc(iy.S.lab)+', '+iy.S.n+' maç): gol olan maç '+P(iy.S.more1)+', 2+ gol olan '+P(iy.S.more2)+'.'+
                          (iy.S.leadWin!=null?' Önde olan devreyi önde kapattı: '+P(iy.S.leadWin)+'.':'')+(iy.S.keepDraw!=null?' Devre berabere bitti: '+P(iy.S.keepDraw)+'.':'')+'</div>';
    out += '<div class="row">Maç sonuna kadar ('+esc(S.lab)+', <b>'+S.n+' maç</b>): en az bir gol olan maç '+P(S.more1)+', iki ve daha fazla gol olan maç '+P(S.more2)+' (maç başı '+S.mean.toFixed(2)+' gol).</div>';
    out += '<div class="row">İlk gol ne zaman geldi: '+P(S.in15)+' ilk 15 dk içinde, '+P(S.in30)+' 30 dk içinde. Sıradaki golü ev sahibi '+P(S.nextH)+', deplasman '+P(S.nextA)+' attı.'+
           (S.leadWin!=null?' Önde olan tarafın kazanma oranı '+P(S.leadWin)+'.':'')+'</div>';
  } else out += '<p class="note">Bu lig için yeterli gol dakikası verisi yok.</p>';

  // 4) Takımların tepkisi
  out += '<div class="sec">Takımlar bu durumda daha önce ne yaptı?</div>';
  out += reactHtml(m.h, o.TM[0], iy && iy.TM[0]) + reactHtml(m.a, o.TM[1], iy && iy.TM[1]);

  // 5) Gol dakikaları
  out += '<div class="sec">'+o.t+'. dakikadan sonra gol eğilimi</div>';
  for(const i of [0,1]){
    const g = o.TM[i] && o.TM[i].gen, gi = iy && iy.TM[i] && iy.TM[i].gen;
    if(g && g.n) out += '<div class="row"><b>'+esc(i?m.a:m.h)+'</b> (son '+g.n+' maç): '+
                      (gi?'<span class="iyt">devreye kadar gol olan maç '+P(gi.any)+' (maç başı '+gi.gf.toFixed(2)+' attı, '+gi.ga.toFixed(2)+' yedi)</span>; ':'')+
                      'maç sonuna kadar gol olan maç '+P(g.any)+', maç başı '+g.gf.toFixed(2)+' attı, '+g.ga.toFixed(2)+' yedi.'+
                      (g.share!=null?' Attığı gollerin bu bölüme düşen payı '+P(g.share)+'.':'')+'</div>';
  }

  // 6) Olasılıklar
  out += '<div class="sec">Şu andan itibaren</div>';
  if(iy){
    out += '<div class="vt">İlk yarı sonu</div><div class="grid">'+box('İY\'de bir gol daha',iy.more1)+box('İY\'de iki gol daha',iy.more2)+box('İY\'de gol yok',1-iy.more1)+'</div>';
    out += '<div class="grid">'+box('İY 1',iy.p1)+box('İY X',iy.px)+box('İY 2',iy.p2)+'</div>';
    out += '<div class="vt">Maç sonu</div>';
  }
  out += '<div class="grid">'+box('Bir gol daha',o.more1)+box('İki gol daha',o.more2)+box('Gol yok',1-o.more1)+'</div>';
  out += '<div class="grid">'+box('MS 1',o.p1)+box('MS X',o.px)+box('MS 2',o.p2)+'</div>';
  const nh=o.nextH, na=o.nextA, nn=1-o.more1;
  out += '<div class="ng"><div style="width:'+nh*100+'%;background:var(--ac)">'+(nh>0.12?esc(m.h)+' '+pct(nh):'')+'</div>'+
         '<div style="width:'+nn*100+'%;background:#888">'+(nn>0.12?'Gol yok '+pct(nn):'')+'</div>'+
         '<div style="width:'+na*100+'%;background:var(--warn)">'+(na>0.12?esc(m.a)+' '+pct(na):'')+'</div></div>';
  out += '<div class="row">Kalan sürede beklenen gol: '+(iy?'devreye kadar <b>'+iy.lh.toFixed(2)+' - '+iy.la.toFixed(2)+'</b>, ':'')+'maç sonuna kadar <b>'+o.lh.toFixed(2)+' - '+o.la.toFixed(2)+'</b></div>';
  const s = L.stats;
  const stats = statRow('Topa sahip olma', s.h.pos, s.a.pos, '%')+statRow('Şut', s.h.sh, s.a.sh)+statRow('İsabetli şut', s.h.sot, s.a.sot)+statRow('Korner', s.h.cor, s.a.cor);
  if(stats) out += '<div class="sec">Maç istatistiği</div>'+stats;
  out += '<details><summary>Maç öncesi tahmin</summary><p class="note">MS 1 '+pct(m.pre.p1)+' · X '+pct(m.pre.px)+' · 2 '+pct(m.pre.p2)+' · 2.5Ü '+pct(m.pre.o25)+' · KG '+pct(m.pre.btts)+'</p></details>';
  return out+'</div>';
}

function doneRow(m, L){
  const tg=L.hg+L.ag, ok25=(m.pre.o25>=0.5)===(tg>=3), okkg=(m.pre.btts>=0.5)===(L.hg>0&&L.ag>0);
  return '<tr><td>'+esc(m.h)+' - '+esc(m.a)+'</td><td class="n"><b>'+L.hg+'-'+L.ag+'</b></td><td class="n '+(ok25?'pos':'neg')+'">'+(ok25?'✓':'✗')+' '+pct(m.pre.o25)+'</td><td class="n '+(okkg?'pos':'neg')+'">'+(okkg?'✓':'✗')+' '+pct(m.pre.btts)+'</td></tr>';
}

async function update(){
  const st = document.getElementById('status');
  st.textContent = 'Güncelleniyor…';
  let D;
  try{ D = await getLiveData(); }
  catch(e){ st.textContent=''; document.getElementById('live').innerHTML='<div class="ban">Model dosyası bulunamadı. Bot bir kez çalıştıktan sonra bu sayfa dolacak.</div>'; return; }
  const {relevant, evs, err, relayAge, now} = D;
  let live='', soon='', done='', wait='';
  const ordered = relevant.slice().sort((a,b)=>Date.parse(a.k)-Date.parse(b.k));
  for(const m of ordered){
    const ev = evs[m.id]; const k = new Date(Date.parse(m.k));
    let L = null; try{ if(ev) L = parseLive(ev); }catch(e){}
    if(L && L.state==='in') live += liveCard(m, L);
    else if(L && L.done) done += doneRow(m, L);
    else if(k.getTime()<=now) wait += '<tr><td>'+hm(k)+'</td><td>'+esc(m.h)+' - '+esc(m.a)+'<br><span class="note">'+esc(m.lg)+'</span></td></tr>';
    else if(k.getTime()>now) soon += '<tr><td>'+hm(k)+'</td><td>'+esc(m.h)+' - '+esc(m.a)+'<br><span class="note">'+esc(m.lg)+'</span></td><td class="n">'+pct(m.pre.o25)+'</td><td class="n">'+pct(m.pre.btts)+'</td></tr>';
  }
  let html = '';
  if(err) html += '<div class="ban">Canlı skor alınamadı ('+esc(err.message||err)+'). Bot maç saatlerinde 20 dakikada bir kontrol edip aktarımı başlatır; birkaç dakika sonra tekrar dene.</div>';
  else if(relayAge!=null && relayAge>5) html += '<div class="ban">Aktarım '+Math.round(relayAge)+' dakikadır güncellenmedi. Bot birkaç dakika içinde yeniden başlayacak.</div>';
  html += live || '<p class="empty">Şu an takip edilen liglerde canlı maç yok.</p>';
  if(wait) html += '<h3>Başlamış, skor bekleniyor</h3><div class="wrap"><table><tr><th>Saat</th><th>Maç</th></tr>'+wait+'</table></div>';
  if(soon) html += '<h3>Yaklaşan (3 saat içinde)</h3><div class="wrap"><table><tr><th>Saat</th><th>Maç</th><th class="n">2.5Ü</th><th class="n">KG</th></tr>'+soon+'</table></div>';
  if(done) html += '<h3>Son biten maçlar</h3><div class="wrap"><table><tr><th>Maç</th><th class="n">Skor</th><th class="n">2.5Ü tahmini</th><th class="n">KG tahmini</th></tr>'+done+'</table></div>';
  document.getElementById('live').innerHTML = html;
  st.textContent = 'Son güncelleme '+new Date().toLocaleTimeString('tr-TR',{timeZone:'Europe/Istanbul'})+(SOURCE?' · kaynak: '+SOURCE:'')+' · her dakika yenilenir';
}
document.getElementById('refresh').addEventListener('click', update);
update(); setInterval(update, 60000);
"""


ALARM_JS = r"""
async function alarmUpdate(){
  const el = document.getElementById('alarm');
  let D;
  try{ D = await getLiveData(); }catch(e){ el.innerHTML=''; return; }
  const live = [];
  for(const m of D.relevant){
    const ev = D.evs[m.id]; if(!ev) continue;
    let L = null; try{ L = parseLive(ev); }catch(e){}
    if(L && L.state==='in') live.push([m, L]);
  }
  if(!live.length){ el.innerHTML=''; return; }
  const al = live.map(([m,L])=>alarmScan(m,L)).filter(Boolean).sort((a,b)=>b.score-a.score);
  const t = new Date().toLocaleTimeString('tr-TR',{hour:'2-digit',minute:'2-digit',timeZone:'Europe/Istanbul'});
  let h = '<div class="alarm"><div class="ah"><span><span class="live">CANLI</span> <b>Alarm</b></span><span class="note">'+
          live.length+' canlı maç tarandı · '+t+'</span></div>';
  if(!al.length) h += '<p class="note" style="margin:6px 0 0">Şu an kanıtları birbirini tutan bir canlı bahis yok. Model, ligdeki benzer maçlar, takımların geçmiş tepkisi ve tempo aynı yönü gösterdiğinde burada belirir.</p>';
  for(const a of al.slice(0,5)){
    const min = a.o.ht ? 'Devre' : (a.L.disp||'');
    h += '<a class="arow '+a.level+'" href="canli.html?v='+Date.now()+'#m'+a.m.id+'">'+
         '<div class="at"><span class="lv">'+(a.level==='kritik'?'KRİTİK':'TAKİPTE')+'</span> '+esc(min)+' · '+esc(a.m.h)+' <b>'+a.L.hg+'-'+a.L.ag+'</b> '+esc(a.m.a)+'</div>'+
         '<div class="ab"><b>'+esc(a.bet.t)+'</b>'+(a.bet.sub?' <span class="note">'+esc(a.bet.sub)+'</span>':'')+' %'+Math.round(a.bet.p*100)+'</div>'+
         (a.reasons.length?'<div class="ar">'+a.reasons.map(esc).join(' · ')+'</div>':'')+'</a>';
  }
  el.innerHTML = h + '</div>';
}
alarmUpdate(); setInterval(alarmUpdate, 90000);
"""


def live_core_js():
    return LIVE_JS[:LIVE_JS.index("function statRow(")]


def write_live_html():
    repo = json.dumps(os.environ.get("GITHUB_REPOSITORY", ""))
    page = (f"<!doctype html><html lang='tr'><head><meta charset='utf-8'>"
            f"<meta name='viewport' content='width=device-width, initial-scale=1'>"
            f"<title>Canlı Maçlar</title><style>{CSS}{LIVE_CSS}</style></head><body>"
            f"<header><div class='top'><h1>Canlı Maçlar</h1><a class='back' href='index.html'>← Günün maçları</a></div>"
            f"<div class='upd'><span id='status'></span> <button class='btn' id='refresh'>Yenile</button></div>"
            f"<p class='note'>Öneriler dört kanıtın birlikte değerlendirilmesidir: model (kalan süre, skor, kırmızı kart, isabetli şut), "
            f"ligde aynı dakikada aynı skordaki maçlar, takımların bu durumdaki geçmiş tepkisi ve maçın temposu. "
            f"Kanıtlar birbirini tutmuyorsa öneri çıkmaz. Tahmindir, kâr garantisi vermez.</p></header>"
            f"<div class='wrapc' id='live'><p class='empty'>Yükleniyor…</p></div><script>const REPO = {repo};{LIVE_JS}</script></body></html>")
    with open("canli.html", "w", encoding="utf-8") as f:
        f.write(page)



# ------------------------------------------------------------ KUPON ANALİZİ (oynamadan önce)
AN_FILE = "data/analiz.json"
DRAFT_FILE = "data/taslaklar.json"


def score_freq(rows):
    """Son maçlarda gol attığı / yediği maç sayısı (maç sonu ve ilk yarı)."""
    r1 = [x for x in rows if x[3] is not None]
    return {"n": len(rows), "s": sum(1 for x in rows if x[1] > 0), "c": sum(1 for x in rows if x[2] > 0),
            "s2": sum(1 for x in rows if x[1] > 1), "c2": sum(1 for x in rows if x[2] > 1),
            "n1": len(r1), "s1": sum(1 for x in r1 if x[3] > 0), "c1": sum(1 for x in r1 if x[4] > 0),
            "s12": sum(1 for x in r1 if x[3] > 1), "c12": sum(1 for x in r1 if x[4] > 1)}


def tc_text(t):
    if not t:
        return ""
    parts = []
    if t.get("rank"):
        parts.append(f"{t['rank']}. sıra ({t['tag']})")
    if t.get("form"):
        parts.append(f"son 5: {t['form']}")
    if t.get("gf") is not None:
        parts.append(f"son 10 maçta maç başı {t['gf']:.1f} attı, {t['ga']:.1f} yedi")
    if t.get("luck") is not None and abs(t["luck"]) >= 3:
        parts.append("şutlarına göre " + ("şanslı gidiyor" if t["luck"] > 0 else "şanssız gidiyor"))
    if t.get("rest") is not None and t["rest"] <= 3:
        parts.append(f"son maçından beri {t['rest']} gün: rotasyon riski")
    return " · ".join(parts)


def analiz_entry(c):
    r = c["r"]
    lam1 = r.get("lam1") or [c["lam"][0] * 0.45, c["lam"][1] * 0.45]
    rp = {}
    for k, v in ((c.get("rapor") or {}).get("m") or {}).items():
        rp[k] = {"p": round(v["p"], 4), "t": v["tier"], "ok": v["ok"], "n": v["tot"],
                 "c": [[int(ok), t] for ok, t in v["checks"]], "i": [[int(ok), t] for ok, t in v.get("info", [])]}
    return {"h": c["home"], "a": c["away"], "lg": c["league"], "k": c["kick"].isoformat(),
            "l": [round(x, 4) for x in (c["lam"][0], c["lam"][1], lam1[0], lam1[1])],
            "p": {k: round(r[k], 4) for k in PRED_KEYS if r.get(k) is not None},
            "rp": rp, "low": bool(c.get("low")), "tsc": c.get("tsc"),
            "tc": {"h": tc_text(c.get("tctx", {}).get("h")), "a": tc_text(c.get("tctx", {}).get("a"))}}


def write_analiz(leagues, now):
    ms = {}
    for L in leagues:
        for c in L.get("cards", []):
            try:
                ms[c["id"]] = analiz_entry(c)
            except Exception as e:  # noqa
                print("analiz verisi yazılamadı:", c.get("id"), e, flush=True)
    trust = {f"{k}|{t}": [round(v["hit"], 3), v["n"], round(v["base"], 3)] for (k, t), v in (TRUST or {}).items()}
    with open(AN_FILE, "w", encoding="utf-8") as f:
        json.dump({"t": now.isoformat(), "trust": trust, "m": ms}, f, ensure_ascii=False, separators=(",", ":"))
    # Bana fotoğrafla gönderilip eklenen taslaklarda maç verisinin kopyasını sakla (maç günü geçince de analiz görünsün)
    try:
        with open(DRAFT_FILE, encoding="utf-8") as f:
            d = json.load(f)
    except Exception:  # noqa
        return
    ch = False
    for k in d.get("kuponlar", []):
        for l in k.get("legs", []):
            if l.get("m") and not l.get("snap") and str(l["m"]) in ms:
                l["snap"] = ms[str(l["m"])]
                ch = True
    if ch:
        with open(DRAFT_FILE, "w", encoding="utf-8") as f:
            json.dump(d, f, ensure_ascii=False, indent=1)


ANALIZ_JS = r"""
let AN = {m:{}, trust:{}};
const RAPOR_OF = {ms1:'ms1',ms2:'ms2',o15:'o15',o25:'o25',o35:'o35',o45:'o45',u25:'u25',kgv:'btts',iyo05:'iy05',iyo15:'iy15',iykgv:'iykg',
                  tev05:'h05',tdp05:'a05',tev15:'h15',tdp15:'a15',tiev05:'ih05',tidp05:'ia05'};
const TIER = {2:'Güçlü',1:'Orta',0:'Zayıf'};
function snapOf(l){ return (l.m && AN.m[l.m]) || l.snap || null; }
// Bir bacağın analizi
function legAn(l){
  const s = snapOf(l), o = {s};
  if(!s){ o.v = 'yok'; return o; }
  const rk = RAPOR_OF[l.b];
  let rp = rk && s.rp ? s.rp[rk] : null;
  o.p = rp ? rp.p : modelP(l.b, {l:s.l, p:s.p});
  if(!rp) rp = teamRp(l.b, s, o.p);
  o.rp = rp;
  if(rp){ const t = AN.trust[rk+'|'+rp.t]; if(t && rp.t>0) o.hist = t; }
  o.imp = (+l.o>1) ? 1/(+l.o) : null;
  if(o.p==null) o.v = 'yok';
  else if(o.imp!=null && o.p < o.imp-0.05) o.v = 'pahali';
  else if(o.p>=0.65 && (!rp || rp.t===2)) o.v = 'guclu';
  else if(o.p>=0.55 && (!rp || rp.t>=1)) o.v = 'iyi';
  else if(o.p<0.5) o.v = 'zayif';
  else o.v = 'belirsiz';
  return o;
}
// Takım golü bahisleri (Ev/Dep, maç sonu ya da ilk yarı): takımın gol attığı ve rakibin gol yediği maç sıklığı
function teamRp(code, s, p){
  const m = code.match(/^t(i?)(ev|dp)(\d)(\d)$/); if(!m || !s.tsc || p==null) return null;
  const iy = !!m[1], ev = m[2]==='ev', two = m[3]==='1';
  const me = ev ? s.tsc.h : s.tsc.a, op = ev ? s.tsc.a : s.tsc.h, nm = ev ? s.h : s.a, on = ev ? s.a : s.h;
  if(!me || !op) return null;
  const k = (iy?'1':'')+(two?'2':''), sk = 's'+k, ck_ = 'c'+k, n1 = iy?me.n1:me.n, n2 = iy?op.n1:op.n;
  const what = (two?'2+ ':'')+'gol'+(iy?' (ilk yarıda)':'');
  const c = [[p>=0.6?1:0, 'Model: '+pc(p)],
             [n1&&me[sk]/n1>=0.6?1:0, nm+' son '+n1+' maçın '+me[sk]+' tanesinde '+what+' attı'],
             [n2&&op[ck_]/n2>=0.6?1:0, on+' son '+n2+' maçın '+op[ck_]+' tanesinde '+what+' yedi']];
  const ok = c.filter(x=>x[0]).length;
  return {p, t: (c[0][0] && ok===3) ? 2 : ((c[0][0] && ok>=2) ? 1 : 0), ok, n:3, c, i:[]};
}
const VLAB = {guclu:['Güçlü','pos'], iyi:['Kupona uygun','pos'], belirsiz:['Belirsiz',''], zayif:['Zayıf halka','neg'], pahali:['Oran modele göre düşük','neg'], yok:['Model verisi yok','']};
function legText(l, a){
  const s = a.s; if(!s) return 'Bu maç modelin takip ettiği liglerde değil ya da maç günü verisi henüz yok; analiz yapılamadı.';
  const lam = s.l, tot = lam[0]+lam[1];
  let t = 'Model maçta toplam '+tot.toFixed(1)+' gol bekliyor ('+s.h+' '+lam[0].toFixed(1)+', '+s.a+' '+lam[1].toFixed(1)+'; ilk yarıda '+(lam[2]+lam[3]).toFixed(1)+'). ';
  if(a.p!=null) t += l.bl+' için tutma ihtimali '+pc(a.p)+'. ';
  if(a.rp) t += 'Kontrol listesinde '+a.rp.ok+'/'+a.rp.n+' kriter tutuyor ('+TIER[a.rp.t]+'). ';
  if(a.hist) t += 'Bu seviyedeki '+l.bl+' önerileri geçmişte '+pc(a.hist[0])+' tuttu ('+a.hist[1]+' maç; tüm maçlarda '+pc(a.hist[2])+'). ';
  if(a.imp!=null) t += 'Girdiğin '+(+l.o).toFixed(2)+' oranı bu bahse '+pc(a.imp)+' ihtimal biçiyor'+(a.p!=null?(a.p<a.imp-0.05?'; model daha az emin.':(a.p>a.imp+0.05?'; model daha emin.':'; model de aynı yerde.')):'.')+' ';
  if(s.low) t += 'Takımlardan birinin geçmiş verisi az, tahmin daha belirsiz. ';
  return t;
}
function legHtml(l, a, i, kid){
  const [vl, vc] = VLAB[a.v];
  let h = '<details class="al"><summary><div class="alh"><span><b>'+esc(l.ad)+'</b><small>'+esc(l.bl)+(+l.o>1?' · '+(+l.o).toFixed(2):'')+'</small></span>'+
          '<span class="alp">'+(a.p!=null?pc(a.p):'-')+'<small class="'+vc+'">'+vl+'</small></span></div></summary>';
  h += '<p class="tx">'+esc(legText(l, a))+'</p>';
  if(a.rp){
    h += '<ul class="ck">'+a.rp.c.map(c=>'<li class="'+(c[0]?'y':'n')+'">'+esc(c[1])+'</li>').join('')+
         a.rp.i.map(c=>'<li class="i">'+esc(c[1])+' <span class="note">· bilgi, '+(c[0]?'lehine':'aleyhine')+'</span></li>').join('')+'</ul>';
  }
  if(a.s && (a.s.tc.h||a.s.tc.a)) h += '<p class="note"><b>'+esc(a.s.h)+'</b>: '+esc(a.s.tc.h)+'<br><b>'+esc(a.s.a)+'</b>: '+esc(a.s.tc.a)+'</p>';
  if(kid) h += '<div style="text-align:right"><button class="btn sm" onclick="delLeg(\''+kid+'\','+i+')">Bu maçı çıkar</button></div>';
  return h+'</details>';
}
function couponSummary(legs, ans){
  const ps = ans.map(a=>a.p), known = ps.filter(x=>x!=null);
  if(!known.length) return '<p class="note">Kupondaki maçlar için model verisi yok.</p>';
  const prod = known.reduce((x,y)=>x*y,1);
  let o = 1; legs.forEach(l=>{ if(+l.o>1) o*=+l.o; });
  let h = '<div class="ksum"><div>Kuponun tutma ihtimali (model)<b>'+pc(prod)+'</b><small>'+(prod>0?'yaklaşık '+Math.max(1,Math.round(1/prod))+' kuponda 1':'')+
          (known.length<legs.length?' · '+(legs.length-known.length)+' maç hesaba katılmadı':'')+'</small></div>';
  if(o>1) h += '<div>Oranların varsaydığı<b>'+pc(1/o)+'</b><small>toplam oran '+o.toFixed(2)+'</small></div>';
  h += '</div>';
  const idx = ans.map((a,i)=>[a.p,i]).filter(x=>x[0]!=null).sort((a,b)=>a[0]-b[0]);
  const weak = idx.filter(x=>x[0]<0.55 || ['zayif','pahali'].includes(ans[x[1]].v));
  if(weak.length){
    const w = weak[0], without = w[0]>0 ? prod/w[0] : null;
    h += '<p class="tx">En zayıf halka: <b>'+esc(legs[w[1]].ad)+' · '+esc(legs[w[1]].bl)+'</b> ('+pc(w[0])+'). '+(without!=null?'Çıkarırsan kuponun ihtimali '+pc(prod)+' → <b>'+pc(without)+'</b>.':'')+
         (weak.length>1?' Riskli görünen diğer maçlar: '+weak.slice(1).map(x=>esc(legs[x[1]].ad.split(' - ')[0])+' ('+pc(x[0])+')').join(', ')+'.':'')+'</p>';
  } else h += '<p class="tx">Kupondaki her maç tek başına %55 ve üstü. Yine de maç sayısı arttıkça birlikte tutma ihtimali hızla düşer.</p>';
  const g = ans.filter(a=>a.v==='guclu'||a.v==='iyi').length;
  h += '<p class="note">'+legs.length+' maçın '+g+' tanesi kupona uygun görünüyor.</p>';
  return h;
}
// --- sayfa: taslak oluşturma (bahis sayfasının fonksiyonlarını değiştirir)
function renderSummary(){ $('sum').innerHTML=''; }
function addLeg(){
  const v = ($('odd').value||'').replace(',','.'), o = v ? parseFloat(v) : null;
  if(v && !(o>1)){ msg('Oran 1\'den büyük olmalı (boş da bırakabilirsin).'); return; }
  const b = $('mk').value;
  draft.push(Object.assign({}, pick, {b:b, bl:MARKETS.find(x=>x[1]===b)[2], o:o, canli:false, sonuc:null}));
  $('legf').style.display='none'; pick=null; msg(''); renderDraft();
}
function renderDraft(){
  const ans = draft.map(legAn);
  $('draft').innerHTML = draft.map((l,i)=>legHtml(l, ans[i]).replace('</details>','<div style="text-align:right"><button class="btn sm" onclick="draft.splice('+i+',1);renderDraft()">Çıkar</button></div></details>')).join('');
  $('tot').innerHTML = draft.length ? couponSummary(draft, ans) : 'Kupon boş: yukarıdan maç seç.';
  $('savebox').style.display = draft.length ? 'block' : 'none';
}
async function saveCoupon(){
  const kp = {id:'t'+Date.now(), t:new Date().toISOString(), not:($('stake').value||'').trim(),
              legs:draft.map(l=>({m:l.m,ad:l.ad,lg:l.lg,k:l.k,b:l.b,bl:l.bl,o:l.o,snap:snapOf(l)}))};
  msg('Kaydediliyor…', true);
  try{ await ghSave(d=>d.kuponlar.push(kp), 'Analiz kuponu eklendi'); draft=[]; $('stake').value=''; renderDraft(); renderAll(); msg('Kaydedildi ✓', true); }
  catch(e){ msg(esc(e.message)); }
}
async function delLeg(id, i){ if(!confirm('Bu maç kupondan çıkarılsın mı?')) return;
  try{ await ghSave(d=>{const k=d.kuponlar.find(k=>k.id===id); if(k) k.legs.splice(i,1);}, 'Analiz kuponu güncellendi'); renderAll(); }catch(e){ msg(esc(e.message)); } }
async function playK(id){
  const k = DATA.kuponlar.find(x=>x.id===id); if(!k) return;
  if(k.legs.some(l=>!(+l.o>1))){ alert('Kayda aktarmak için her maçın oranı girilmiş olmalı.'); return; }
  const t = parseFloat((prompt('Kupon bedeli (TL):')||'').replace(',','.')); if(!(t>0)) return;
  const kp = {id:'k'+Date.now(), t:new Date().toISOString(), tutar:t, kaynak:'analiz sayfası',
              legs:k.legs.map(l=>{ const a=legAn(l); return {m:l.m,ad:l.ad,lg:l.lg,k:l.k,b:l.b,bl:l.bl,o:+l.o,canli:false,sonuc:null,mp:a.p==null?null:Math.round(a.p*1e4)/1e4}; })};
  const P = 'https://api.github.com/repos/'+REPO+'/contents/data/bahislerim.json';
  try{
    for(let i=0;i<3;i++){
      const r = await fetch(P+'?ref=main&t='+Date.now(), {headers:{Authorization:'Bearer '+tok(), Accept:'application/vnd.github+json'}, cache:'no-store'});
      let data={kuponlar:[]}, sha=null; if(r.ok){ const j=await r.json(); data=JSON.parse(b64d(j.content)); sha=j.sha; }
      data.kuponlar=(data.kuponlar||[]); data.kuponlar.push(kp);
      const body={message:'Kupon eklendi (analizden)', content:b64e(JSON.stringify(data,null,1)), branch:'main'}; if(sha) body.sha=sha;
      const w = await fetch(P, {method:'PUT', headers:{Authorization:'Bearer '+tok(), Accept:'application/vnd.github+json','Content-Type':'application/json'}, body:JSON.stringify(body)});
      if(w.ok){ msg('Kupon kayıtlarına eklendi ✓', true); return; }
      if(w.status!==409 && w.status!==422) throw new Error('GitHub '+w.status);
    }
  }catch(e){ msg('Aktarılamadı: '+esc(e.message)); }
}
function renderCoupons(){
  const ks = DATA.kuponlar.slice().sort((a,b)=>(b.t||'').localeCompare(a.t||''));
  $('kps').innerHTML = ks.map((k,j)=>{
    const ans = k.legs.map(legAn), known = ans.filter(a=>a.p!=null), prod = known.reduce((x,a)=>x*a.p,1);
    return '<details class="kp"'+(j===0?' open':'')+'><summary><div class="kh"><span>'+dm(dayOf(k.t))+' '+hm(k.t)+' · '+k.legs.length+' maç'+(k.not?' · '+esc(k.not):'')+'</span>'+
      '<span>'+(known.length?'model '+pc(prod):'')+'</span></div><div class="ks">'+esc(k.legs.map(l=>l.ad.split(' - ')[0]).slice(0,3).join(', '))+(k.legs.length>3?' …':'')+'</div></summary>'+
      couponSummary(k.legs, ans)+k.legs.map((l,i)=>legHtml(l, ans[i], i, k.id)).join('')+
      '<div style="text-align:right;margin-top:8px"><button class="btn sm pri" onclick="playK(\''+k.id+'\')">Oynadım: kupon kaydına ekle</button> '+
      '<button class="btn sm" onclick="delK(\''+k.id+'\')">Sil</button></div></details>'; }).join('') ||
    '<p class="empty">Henüz analiz edilen kupon yok. Yukarıdan kupon oluştur ya da kupon fotoğrafını Claude\'a gönder.</p>';
}
"""

ANALIZ_CSS = """
.al{border:1px solid var(--bd);border-radius:10px;padding:8px 10px;margin:6px 0;background:var(--card)}
.al summary{list-style:none;cursor:pointer}.al summary::-webkit-details-marker{display:none}
.alh{display:flex;justify-content:space-between;gap:8px;align-items:center}
.alh small{display:block;color:var(--mu);font-size:12px;font-weight:400}
.alp{text-align:right;font-size:18px;font-weight:800;white-space:nowrap}.alp small{font-size:11.5px;font-weight:700}
.tx{font-size:13.5px;line-height:1.5;margin:8px 0}
.ksum{display:flex;gap:10px;margin:8px 0}.ksum div{flex:1;border:1px solid var(--bd);border-radius:10px;padding:8px;font-size:12px;color:var(--mu)}
.ksum b{display:block;font-size:22px;color:var(--tx);margin:2px 0}.ksum small{display:block;font-size:11px}
"""


def write_analiz_html():
    repo = json.dumps(os.environ.get("GITHUB_REPOSITORY", "") or "nattbot2302/nattbot")
    js = (BET_JS.replace("__REPO__", repo).replace("__MARKETS__", json.dumps(BET_MARKETS, ensure_ascii=False))
          .replace("/contents/data/bahislerim.json", "/contents/" + DRAFT_FILE)
          .replace("fetch('data/bahislerim.json?t='", "fetch('" + DRAFT_FILE + "?t='")
          .replace("renderDays(); renderList(); renderDraft();",
                   "try{ const r = await fetch('" + AN_FILE + "?t='+Date.now()); if(r.ok) AN = await r.json(); }catch(e){}\n  renderDays(); renderList(); renderDraft();")
          .replace("\ninit();\n", "\n" + ANALIZ_JS + "\ninit();\n"))
    page = (f"<!doctype html><html lang='tr'><head><meta charset='utf-8'>"
            f"<meta name='viewport' content='width=device-width, initial-scale=1'>"
            f"<title>Kupon Analizi</title><style>{CSS}{BET_CSS}{RP_CSS}{ANALIZ_CSS}</style></head><body>"
            "<header><div class='top'><h1>Kupon Analizi</h1><a class='back' href='index.html'>← Günün maçları</a></div>"
            "<p class='note'>Oynamayı düşündüğün kuponu buraya gir ya da fotoğrafını Claude'a gönder; her maç için modelin tutma "
            "ihtimali, kontrol listesi ve gerekçesi çıkar. Oran girmek isteğe bağlı: girersen oranın varsaydığı ihtimalle kıyaslanır. "
            "Analiz, botun o günkü verisiyle yapılır (yarının maçları sabah 08:00 çalışmasından sonra gelir).</p></header>"
            "<div class='wrapb'><div id='sum'></div>"
            "<div class='card'><h2>Yeni kupon</h2>"
            "<div class='row2'><select id='day' class='sel' onchange=\"$('q').value='';renderList()\"></select>"
            "<input id='q' class='in' placeholder='Takım ara' oninput='renderList()'></div>"
            "<div id='ml' class='mlist'></div>"
            "<div id='legf' class='legf' style='display:none'><div id='legt' class='leg' style='border:0'></div>"
            "<select id='mk' class='sel'></select>"
            "<div class='row2'><input id='odd' class='in' inputmode='decimal' placeholder='Oran (isteğe bağlı)'></div>"
            "<span id='b-pre'></span><span id='b-on'></span>"
            "<div class='row2'><button class='btn pri' onclick='addLeg()'>Kupona ekle</button>"
            "<button class='btn' onclick=\"$('legf').style.display='none'\">Vazgeç</button></div></div>"
            "<div class='sec'>Kupon</div><div id='draft'></div><div id='tot' class='tot'></div>"
            "<div id='savebox' style='display:none'><input id='stake' class='in' placeholder='Not (isteğe bağlı, örn. akşam kuponu)'>"
            "<div class='row2'><button class='btn pri' onclick='saveCoupon()'>Analizi kaydet</button></div></div>"
            "<div id='msg' class='msg'></div></div>"
            "<h2 style='margin-top:16px'>Analiz edilen kuponlar</h2><div id='kps'></div>"
            "<details class='rp' style='margin-top:14px'><summary><b>Ayarlar: GitHub anahtarı</b> <span id='tks' class='note'></span></summary>"
            "<div class='tc'>Kupon sayfasında girdiğin anahtar burada da geçerlidir (aynı telefon ve tarayıcı).</div>"
            "<div class='row2'><input id='tk' class='in' type='password' placeholder='github_pat_…'><button class='btn' onclick='saveTok()'>Kaydet</button></div></details>"
            f"</div><script>{js}</script></body></html>")
    with open("analiz.html", "w", encoding="utf-8") as f:
        f.write(page)


# -------------------------------------------------------------------- CANLI AKTARIM
# Telefon tarayıcısı ESPN'e doğrudan bağlanamadığı için, maç saatlerinde GitHub'da bu döngü
# her dakika skorları çeker ve "canli" dalındaki canli.json dosyasına yazar.
RELAY_BRANCH = "canli"
RELAY_DIR = "/tmp/canli-relay"
LIVE_BEFORE = 40      # maç başlamadan kaç dakika önce aktarım başlasın
LIVE_AFTER = 150      # başlama saatinden kaç dakika sonrasına kadar izlensin
LIVE_MAX_H = 5.6      # tek çalıştırmanın en uzun süresi (GitHub sınırı 6 saat)
STAT_NAMES = {"possessionPct", "totalShots", "shotsOnTarget", "wonCorners"}


def trim_event(ev):
    c = ev["competitions"][0]
    return {
        "id": ev["id"], "status": ev.get("status", {}),
        "competitions": [{
            "competitors": [{
                "homeAway": x.get("homeAway"), "score": x.get("score"),
                "team": {"id": (x.get("team") or {}).get("id")},
                "statistics": [s for s in x.get("statistics", []) if s.get("name") in STAT_NAMES],
            } for x in c.get("competitors", [])],
            "details": [{"redCard": True, "team": {"id": (d.get("team") or {}).get("id")}}
                        for d in c.get("details", []) if d.get("redCard")],
        }],
    }


def relevant_matches(model, now):
    out = []
    for m in model.get("matches", []):
        k = dt.datetime.fromisoformat(m["k"])
        mins = (now - k).total_seconds() / 60
        if -LIVE_BEFORE <= mins <= LIVE_AFTER:
            out.append(m)
    return out


LIVE_HIST = {}      # maç -> [[dakika, ev şut, dep şut, ev isabetli, dep isabetli, ev korner, dep korner], ...]


def add_hist(ev):
    try:
        st = ev.get("status", {})
        if st.get("type", {}).get("state") != "in":
            return
        mn = round((st.get("clock") or 0) / 60, 1)
        c = ev["competitions"][0]["competitors"]
        side = {x.get("homeAway"): {s.get("name"): s.get("displayValue") for s in x.get("statistics", [])} for x in c}

        def v(h, k):
            try:
                return float(side[h].get(k))
            except (TypeError, ValueError, KeyError):
                return None
        row = [mn, v("home", "totalShots"), v("away", "totalShots"), v("home", "shotsOnTarget"),
               v("away", "shotsOnTarget"), v("home", "wonCorners"), v("away", "wonCorners")]
        if row[1] is None:
            return
        h = LIVE_HIST.setdefault(ev["id"], [])
        if h and mn - h[-1][0] < 1.0:
            h[-1] = row            # aynı dakika: son değeri tut
        else:
            h.append(row)
        del h[:-60]
        ev["hist"] = h
    except Exception:  # noqa
        pass


def relay_snapshot(rel):
    want = {m["id"] for m in rel}
    dates = defaultdict(set)
    for m in rel:
        k = dt.datetime.fromisoformat(m["k"])
        dates[m["slug"]] |= {f"{k:%Y%m%d}", f"{k - dt.timedelta(days=1):%Y%m%d}"}
    events = {}
    for slug, ds in dates.items():
        for d in sorted(ds):
            try:
                data = http_json(BASE.format(slug=slug), {"dates": d})
            except Exception as e:  # noqa
                print("  alınamadı:", slug, d, e, flush=True)
                continue
            for ev in data.get("events", []):
                if ev.get("id") in want:
                    try:
                        events[ev["id"]] = trim_event(ev)
                        add_hist(events[ev["id"]])
                    except Exception:  # noqa
                        pass
    return events


def sh(*args, cwd=None, check=True):
    import subprocess
    r = subprocess.run(list(args), cwd=cwd, capture_output=True, text=True)
    if check and r.returncode != 0:
        raise RuntimeError(f"{' '.join(args[:3])}: {r.stderr.strip()[:200]}")
    return r.stdout


def relay_setup():
    import shutil
    ws = os.getcwd()
    url = sh("git", "config", "--get", "remote.origin.url", cwd=ws).strip()
    hdr = sh("git", "config", "--get", "http.https://github.com/.extraheader", cwd=ws, check=False).strip()
    shutil.rmtree(RELAY_DIR, ignore_errors=True)
    os.makedirs(RELAY_DIR)
    sh("git", "init", "-q", "-b", RELAY_BRANCH, cwd=RELAY_DIR)
    sh("git", "remote", "add", "origin", url, cwd=RELAY_DIR)
    if hdr:
        sh("git", "config", "http.https://github.com/.extraheader", hdr, cwd=RELAY_DIR)
    sh("git", "config", "user.name", "bot", cwd=RELAY_DIR)
    sh("git", "config", "user.email", "bot@users.noreply.github.com", cwd=RELAY_DIR)
    return ws


def relay_push(payload, first):
    with open(os.path.join(RELAY_DIR, "canli.json"), "w", encoding="utf-8") as f:
        json.dump(payload, f, ensure_ascii=False, separators=(",", ":"))
    sh("git", "add", "canli.json", cwd=RELAY_DIR)
    if first:
        sh("git", "commit", "-q", "-m", "canlı skorlar", cwd=RELAY_DIR)
    else:
        sh("git", "commit", "-q", "--amend", "-m", "canlı skorlar", cwd=RELAY_DIR)
    sh("git", "push", "-q", "-f", "origin", RELAY_BRANCH, cwd=RELAY_DIR)   # tek commit tutulur, geçmiş şişmez


def load_live_model(ws):
    sh("git", "fetch", "-q", "origin", "main", cwd=ws, check=False)
    try:
        return json.loads(sh("git", "show", f"origin/main:{LIVE_MODEL}", cwd=ws))
    except Exception:  # noqa
        with open(os.path.join(ws, LIVE_MODEL), encoding="utf-8") as f:
            return json.load(f)


def live_loop():
    start = time.time()
    ws = os.getcwd()
    model = load_live_model(ws)
    rel = relevant_matches(model, dt.datetime.now(UTC))
    if not rel:
        print("Şu an canlı ya da yaklaşan maç yok, çıkılıyor.")
        return
    relay_setup()
    first, n = True, 0
    while time.time() - start < LIVE_MAX_H * 3600:
        t0 = time.time()
        if n and n % 10 == 0:
            model = load_live_model(ws)          # 14:00 çalıştırması modeli tazelemiş olabilir
        now = dt.datetime.now(UTC)
        rel = relevant_matches(model, now)
        if not rel:
            print("İzlenecek maç kalmadı.")
            break
        events = relay_snapshot(rel)
        live = sum(1 for e in events.values() if e["status"].get("type", {}).get("state") == "in")
        try:
            relay_push({"t": now.isoformat(), "events": events}, first)
            first = False
        except Exception as e:  # noqa
            print("  yazılamadı:", e, flush=True)
        n += 1
        print(f"{now:%H:%M:%S} izlenen {len(rel)} maç, canlı {live}", flush=True)
        time.sleep(max(5, 60 - (time.time() - t0)))



if __name__ == "__main__":
    import sys
    if len(sys.argv) > 1 and sys.argv[1] == "canli":
        live_loop()
    else:
        main()
