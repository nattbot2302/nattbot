import time
import math
import html
import bisect
import datetime as dt
from collections import defaultdict

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
    ("ger.3", "Almanya 3. Lig", False),
    ("usa.1", "ABD MLS", True),
    ("bra.1", "Brezilya 1. Lig", True),
    ("sui.1", "İsviçre 1. Lig", False),
    ("swe.1", "İsveç 1. Lig", True),
    ("nor.1", "Norveç 1. Lig", True),
    ("den.1", "Danimarka 1. Lig", False),
    ("sco.1", "İskoçya 1. Lig", False),
    ("fra.2", "Fransa 2. Lig", False),
]

HISTORY_DAYS = 420      # geçmiş veri penceresi
HALF_LIFE = 100         # gün: zaman ağırlığı yarı ömrü
LAST_N = 10             # takımın son N maçı
BOOST = 2.5             # son N maça ek ağırlık çarpanı
PRIOR = 3.0             # az maçı olan takımı lige çeken "sanal maç" sayısı
BACKTEST_DAYS = 60


# ---------------------------------------------------------------- veri çekme
HEADERS = {
    "User-Agent": ("Mozilla/5.0 (iPhone; CPU iPhone OS 17_0 like Mac OS X) "
                   "AppleWebKit/605.1.15 (KHTML, like Gecko) Version/17.0 "
                   "Mobile/15E148 Safari/604.1"),
    "Accept": "application/json",
}


def http_json(url, params):
    last = "bilinmiyor"
    params = dict(params)
    for _ in range(3):
        r = None
        try:
            r = requests.get(url, params=params, headers=HEADERS, timeout=30)
            if r.status_code == 400 and "limit" in params:
                params.pop("limit")      # limit parametresini reddederse onsuz dene
                continue
            r.raise_for_status()
            return r.json()
        except requests.HTTPError:
            last = f"HTTP {r.status_code} {r.text[:80]}"
        except Exception as e:  # noqa
            last = f"{type(e).__name__} {str(e)[:80]}"
        time.sleep(2)
    raise RuntimeError(last)


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
    return {
        "id": ev["id"], "date": date,
        "hid": home["team"]["id"], "aid": away["team"]["id"],
        "home": name(home), "away": name(away),
        "hg": score(home), "ag": score(away),
        "done": bool(st.get("completed")), "state": st.get("state", ""),
    }


def fetch_league(slug, now):
    """Son HISTORY_DAYS gün + yarına kadar olan tüm maçlar."""
    events = {}
    start = now.date() - dt.timedelta(days=HISTORY_DAYS)
    end = now.date() + dt.timedelta(days=1)
    d = start
    while d <= end:
        d2 = min(d + dt.timedelta(days=44), end)
        data = http_json(BASE.format(slug=slug),
                         {"dates": f"{d:%Y%m%d}-{d2:%Y%m%d}", "limit": 500})
        for ev in data.get("events", []):
            try:
                m = parse_event(ev)
            except Exception:  # noqa
                m = None
            if m:
                events[m["id"]] = m
        d = d2 + dt.timedelta(days=1)
        time.sleep(0.3)
    allm = sorted(events.values(), key=lambda m: m["date"])
    finished = [m for m in allm if m["done"] and m["hg"] is not None and m["ag"] is not None]
    return finished, allm


# --------------------------------------------------------------------- model
def fit(matches, ref):
    """Zaman ağırlıklı + son-10 vurgulu, rakip gücüne göre düzeltilmiş Poisson modeli."""
    if len(matches) < 30:
        return None
    n = len(matches)
    tw = [0.5 ** (max((ref - m["date"]).days, 0) / HALF_LIFE) for m in matches]

    byteam = defaultdict(list)
    for i, m in enumerate(matches):
        byteam[m["hid"]].append(i)
        byteam[m["aid"]].append(i)
    recent = set()
    for t, idx in byteam.items():
        for i in idx[-LAST_N:]:          # matches tarih sıralı
            recent.add((t, i))

    wh = [tw[i] * (BOOST if (matches[i]["hid"], i) in recent else 1.0) for i in range(n)]
    wa = [tw[i] * (BOOST if (matches[i]["aid"], i) in recent else 1.0) for i in range(n)]

    sw = sum(tw)
    lg_h = sum(tw[i] * matches[i]["hg"] for i in range(n)) / sw
    lg_a = sum(tw[i] * matches[i]["ag"] for i in range(n)) / sw
    lg_h, lg_a = max(lg_h, 0.2), max(lg_a, 0.2)
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
    return {"att": att, "dfn": dfn, "base": base, "ha": ha}


def lambdas(model, h, a):
    if not model or h not in model["att"] or a not in model["att"]:
        return None
    b, ha = model["base"], model["ha"]
    lam_h = b * ha * model["att"][h] * model["dfn"][a]
    lam_a = b / ha * model["att"][a] * model["dfn"][h]
    return min(max(lam_h, 0.15), 5.0), min(max(lam_a, 0.15), 5.0)


def pois(k, lam):
    return math.exp(-lam) * lam ** k / math.factorial(k)


def analyze(lam_h, lam_a, n=9):
    grid = {(i, j): pois(i, lam_h) * pois(j, lam_a) for i in range(n) for j in range(n)}
    tot = sum(grid.values())
    grid = {k: v / tot for k, v in grid.items()}
    s = lambda f: sum(p for (i, j), p in grid.items() if f(i, j))  # noqa
    top = sorted(grid.items(), key=lambda x: -x[1])[:3]
    return {
        "p1": s(lambda i, j: i > j), "px": s(lambda i, j: i == j), "p2": s(lambda i, j: i < j),
        "o15": s(lambda i, j: i + j >= 2), "o25": s(lambda i, j: i + j >= 3),
        "btts": s(lambda i, j: i >= 1 and j >= 1),
        "top": [(f"{i}-{j}", p) for (i, j), p in top],
    }


def similar(model, matches, lam_h, lam_a, k=3):
    sc = []
    for m in matches:
        lam = lambdas(model, m["hid"], m["aid"])
        if lam:
            sc.append(((lam[0] - lam_h) ** 2 + (lam[1] - lam_a) ** 2, m))
    sc.sort(key=lambda x: x[0])
    return [f"{m['date']:%d.%m.%Y} {m['home']} {m['hg']}-{m['ag']} {m['away']}"
            for _, m in sc[:k]]


# ------------------------------------------------------------ takım istatistik
def team_history(matches):
    th = defaultdict(list)
    for m in matches:
        th[m["hid"]].append((m["date"], m["hg"], m["ag"]))
        th[m["aid"]].append((m["date"], m["ag"], m["hg"]))
    return th


def summarize(rows):
    n = len(rows)
    if n == 0:
        return None
    gf = sum(r[1] for r in rows)
    ga = sum(r[2] for r in rows)
    return {
        "n": n, "gf": gf / n, "ga": ga / n,
        "w": sum(1 for r in rows if r[1] > r[2]),
        "d": sum(1 for r in rows if r[1] == r[2]),
        "l": sum(1 for r in rows if r[1] < r[2]),
        "o25": sum(1 for r in rows if r[1] + r[2] >= 3) / n,
        "btts": sum(1 for r in rows if r[1] > 0 and r[2] > 0) / n,
    }


def season_start(now, calendar):
    if calendar:
        return dt.datetime(now.year, 1, 1, tzinfo=UTC)
    y = now.year if now.month >= 7 else now.year - 1
    return dt.datetime(y, 7, 1, tzinfo=UTC)


# ------------------------------------------------------------ geriye dönük test
def backtest(matches, now):
    out = []
    if len(matches) < 60:
        return out
    dates = [m["date"] for m in matches]
    t0 = now - dt.timedelta(days=BACKTEST_DAYS)
    days = sorted({m["date"].date() for m in matches if m["date"] >= t0})
    for d in days:
        ref = dt.datetime(d.year, d.month, d.day, tzinfo=UTC)
        idx = bisect.bisect_left(dates, ref)
        model = fit(matches[:idx], ref)
        if not model:
            continue
        for m in matches[idx:]:
            if m["date"].date() != d:
                continue
            lam = lambdas(model, m["hid"], m["aid"])
            if not lam:
                continue
            r = analyze(*lam)
            tg = m["hg"] + m["ag"]
            out.append({
                "o15": r["o15"], "o25": r["o25"], "btts": r["btts"],
                "p": (r["p1"], r["px"], r["p2"]),
                "a15": tg >= 2, "a25": tg >= 3, "abtts": m["hg"] > 0 and m["ag"] > 0,
                "res": 0 if m["hg"] > m["ag"] else (1 if m["hg"] == m["ag"] else 2),
            })
    return out


def bt_metrics(rows):
    n = len(rows)
    if n == 0:
        return None
    acc = lambda pk, ak: sum(1 for r in rows if (r[pk] >= 0.5) == r[ak]) / n  # noqa
    return {
        "n": n,
        "x2": sum(1 for r in rows if max(range(3), key=lambda i: r["p"][i]) == r["res"]) / n,
        "o25": acc("o25", "a25"), "o15": acc("o15", "a15"), "btts": acc("btts", "abtts"),
        "p25": sum(r["o25"] for r in rows) / n,
        "r25": sum(1 for r in rows if r["a25"]) / n,
        "brier25": sum((r["o25"] - (1 if r["a25"] else 0)) ** 2 for r in rows) / n,
    }


def calibration(rows, pk, ak):
    edges = [0, 0.4, 0.5, 0.6, 0.7, 1.01]
    res = []
    for lo, hi in zip(edges, edges[1:]):
        sel = [r for r in rows if lo <= r[pk] < hi]
        if sel:
            res.append((lo, hi, len(sel), sum(r[pk] for r in sel) / len(sel),
                        sum(1 for r in sel if r[ak]) / len(sel)))
    return res


# ---------------------------------------------------------------- ana akış
def pct(x):
    return f"{x * 100:.0f}%"


def cls(x):
    return "hi" if x >= 0.6 else ("mid" if x >= 0.45 else "lo")


def process_league(slug, name, calendar, now):
    info = {"slug": slug, "name": name, "cards": [], "err": "", "nfin": 0,
            "avg90": None, "bt": []}
    try:
        finished, allm = fetch_league(slug, now)
    except Exception as e:  # noqa
        info["err"] = f"Veri alınamadı: {e}"
        return info
    info["nfin"] = len(finished)
    if len(finished) < 30:
        info["err"] = f"Yetersiz geçmiş veri ({len(finished)} maç)"
        return info

    c90 = [m for m in finished if m["date"] >= now - dt.timedelta(days=90)]
    if c90:
        info["avg90"] = sum(m["hg"] + m["ag"] for m in c90) / len(c90)

    model = fit(finished, now)
    th = team_history(finished)
    ss = season_start(now, calendar)
    today = now.astimezone(TR).date()
    todays = [m for m in allm if m["date"].astimezone(TR).date() == today]

    def tstat(tid):
        rows = sorted(th.get(tid, []), key=lambda r: r[0])
        return summarize(rows[-LAST_N:]), summarize([r for r in rows if r[0] >= ss])

    for m in todays:
        lam = lambdas(model, m["hid"], m["aid"])
        if not lam:
            continue
        r = analyze(*lam)
        info["cards"].append({
            "time": m["date"].astimezone(TR).strftime("%H:%M"),
            "home": m["home"], "away": m["away"], "lam": lam, "r": r,
            "state": m["state"], "score": (m["hg"], m["ag"]) if m["done"] else None,
            "hs": tstat(m["hid"]), "as": tstat(m["aid"]),
            "sim": similar(model, finished, *lam),
        })
    info["cards"].sort(key=lambda c: c["time"])
    info["bt"] = backtest(finished, now)
    return info


def main():
    now = dt.datetime.now(UTC)
    leagues = []
    for slug, name, cal in LEAGUES:
        print("Lig:", slug, flush=True)
        leagues.append(process_league(slug, name, cal, now))
    write_html(leagues, now)


# -------------------------------------------------------------------- HTML
CSS = """
:root{--bg:#f4f5f7;--card:#fff;--tx:#1a1a1a;--mu:#666;--hi:#c8f0d2;--mid:#fdf0c4;--lo:#eee;--ac:#0a7d3b;--bd:#ddd}
@media (prefers-color-scheme:dark){:root{--bg:#111;--card:#1c1c1e;--tx:#eee;--mu:#999;--hi:#1f5130;--mid:#5a4a14;--lo:#2a2a2c;--ac:#3ecf72;--bd:#333}}
*{box-sizing:border-box}
body{margin:0;background:var(--bg);color:var(--tx);font-family:system-ui,sans-serif}
header{padding:12px 12px 0}h1{font-size:20px;margin:0}
.upd{color:var(--mu);font-size:12px;margin:6px 0}
nav{position:sticky;top:0;background:var(--bg);display:flex;gap:6px;overflow-x:auto;padding:8px 12px;z-index:5;white-space:nowrap}
nav button{border:1px solid var(--bd);background:var(--card);color:var(--tx);border-radius:16px;padding:7px 12px;font-size:13px;flex:none}
nav button.on{background:var(--ac);color:#fff;border-color:var(--ac)}
nav small{opacity:.7}
.tab{display:none;padding:4px 12px 24px}.tab.on{display:block}
h2{font-size:17px;margin:4px 0 8px}h3{font-size:15px;margin:14px 0 6px}
.card{background:var(--card);border-radius:12px;padding:14px;margin-bottom:12px}
.meta,.row{color:var(--mu);font-size:13px;margin-top:6px}
.grid{display:grid;grid-template-columns:repeat(3,1fr);gap:8px}
.b{text-align:center;border-radius:8px;padding:8px 4px;font-size:13px}
.b b{font-size:18px}.hi{background:var(--hi)}.mid{background:var(--mid)}.lo{background:var(--lo)}
.sc{float:right;font-weight:600;color:var(--tx)}
.wrap{overflow-x:auto}
table{border-collapse:collapse;width:100%;font-size:12.5px}
th,td{padding:6px 5px;text-align:left;border-bottom:1px solid var(--bd);white-space:nowrap}
th{color:var(--mu);font-weight:600}
td.n,th.n{text-align:right}
summary{margin-top:8px;font-size:13px}li{font-size:13px;color:var(--mu)}
.fire{color:var(--ac);font-weight:700}
.empty,.err{color:var(--mu);font-size:14px;padding:12px 0}
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


def fmt_ts(s):
    if not s:
        return "<td colspan='3'>veri yok</td>"
    return (f"<td class='n'>{s['gf']:.1f}</td><td class='n'>{s['ga']:.1f}</td>"
            f"<td>{s['w']}G {s['d']}B {s['l']}M</td>")


def card_html(c):
    e = html.escape
    r = c["r"]
    top = ", ".join(f"{s} ({pct(p)})" for s, p in r["top"])
    sim = "".join(f"<li>{e(s)}</li>" for s in c["sim"])
    badge = ""
    if c["score"]:
        badge = f"<span class='sc'>Bitti {c['score'][0]}-{c['score'][1]}</span>"
    elif c["state"] == "in":
        badge = "<span class='sc'>Canlı</span>"

    def rows(name, st):
        l10, ssn = st
        return (f"<tr><td>{e(name)}</td>{fmt_ts(l10)}"
                f"<td class='n'>{pct(l10['o25']) if l10 else '-'}</td>"
                f"<td class='n'>{pct(l10['btts']) if l10 else '-'}</td>"
                f"<td class='n'>{ssn['n'] if ssn else 0}</td>"
                f"<td class='n'>{ssn['gf']:.1f}</td><td class='n'>{ssn['ga']:.1f}</td></tr>"
                if ssn else
                f"<tr><td>{e(name)}</td>{fmt_ts(l10)}"
                f"<td class='n'>{pct(l10['o25']) if l10 else '-'}</td>"
                f"<td class='n'>{pct(l10['btts']) if l10 else '-'}</td>"
                f"<td class='n'>0</td><td class='n'>-</td><td class='n'>-</td></tr>")

    return f"""
<div class="card">
  <div class="meta">{c['time']} {badge}</div>
  <h2>{e(c['home'])} - {e(c['away'])}</h2>
  <div class="grid">
    <div class="b {cls(r['o15'])}">1.5 Üst<br><b>{pct(r['o15'])}</b></div>
    <div class="b {cls(r['o25'])}">2.5 Üst<br><b>{pct(r['o25'])}</b></div>
    <div class="b {cls(r['btts'])}">KG Var<br><b>{pct(r['btts'])}</b></div>
  </div>
  <div class="row">MS1 {pct(r['p1'])} · MSX {pct(r['px'])} · MS2 {pct(r['p2'])}</div>
  <div class="row">Beklenen gol: {c['lam'][0]:.2f} - {c['lam'][1]:.2f} (toplam {c['lam'][0] + c['lam'][1]:.2f})</div>
  <div class="row">Olası skorlar: {top}</div>
  <div class="wrap"><table>
    <tr><th></th><th class="n">S10 At</th><th class="n">S10 Ye</th><th>S10 G-B-M</th>
    <th class="n">2.5Ü</th><th class="n">KG</th><th class="n">Sezon maç</th><th class="n">At</th><th class="n">Ye</th></tr>
    {rows(c['home'], c['hs'])}
    {rows(c['away'], c['as'])}
  </table></div>
  <details><summary>Benzer geçmiş maçlar</summary><ul>{sim}</ul></details>
</div>"""


def summary_tab(leagues):
    e = html.escape
    act = []
    for L in leagues:
        if L["cards"]:
            exp = sum(c["lam"][0] + c["lam"][1] for c in L["cards"]) / len(L["cards"])
            o25 = sum(c["r"]["o25"] for c in L["cards"]) / len(L["cards"])
            act.append((exp, o25, L))
    act.sort(key=lambda x: -x[0])
    out = "<h2>Günün özeti</h2>"
    if act:
        out += (f"<p><span class='fire'>Günün en golcü ligi: {e(act[0][2]['name'])}</span> "
                f"(maç başı beklenen {act[0][0]:.2f} gol)</p>")
    else:
        out += "<p class='empty'>Bugün takip edilen liglerde analiz edilebilen maç yok.</p>"
    out += "<div class='wrap'><table><tr><th>Lig</th><th class='n'>Maç</th><th class='n'>Bekl. gol</th><th class='n'>2.5Ü</th><th class='n'>Son 90g gerçek</th></tr>"
    for exp, o25, L in act:
        a90 = f"{L['avg90']:.2f}" if L["avg90"] else "-"
        out += (f"<tr><td>{e(L['name'])}</td><td class='n'>{len(L['cards'])}</td>"
                f"<td class='n'>{exp:.2f}</td><td class='n'>{pct(o25)}</td><td class='n'>{a90}</td></tr>")
    out += "</table></div>"

    allc = [(c, L["name"]) for L in leagues for c in L["cards"]]
    allc.sort(key=lambda x: -x[0]["r"]["o25"])
    if allc:
        out += "<h3>En yüksek 2.5 Üst olasılıklı 8 maç</h3><div class='wrap'><table>"
        out += "<tr><th>Maç</th><th>Lig</th><th class='n'>2.5Ü</th><th class='n'>KG</th></tr>"
        for c, ln in allc[:8]:
            out += (f"<tr><td>{c['time']} {e(c['home'])} - {e(c['away'])}</td><td>{e(ln)}</td>"
                    f"<td class='n'>{pct(c['r']['o25'])}</td><td class='n'>{pct(c['r']['btts'])}</td></tr>")
        out += "</table></div>"

    errs = [f"{L['name']}: {L['err']}" for L in leagues if L["err"]]
    if errs:
        out += "<h3>Sorunlu ligler</h3>" + "".join(f"<p class='err'>{e(x)}</p>" for x in errs)
    return out


def accuracy_tab(leagues):
    e = html.escape
    allrows = [r for L in leagues for r in L["bt"]]
    out = (f"<h2>Model doğruluğu</h2><p class='row'>Son {BACKTEST_DAYS} gün: her maç, "
           "yalnızca o günden önceki verilerle tahmin edilip gerçek sonuçla kıyaslandı. "
           "İsabet = %50 üstü tahminin tutma oranı.</p>")
    out += "<div class='wrap'><table><tr><th>Lig</th><th class='n'>Maç</th><th class='n'>MS</th><th class='n'>2.5</th><th class='n'>1.5</th><th class='n'>KG</th><th class='n'>2.5Ü tahmin</th><th class='n'>2.5Ü gerçek</th></tr>"
    for L in leagues + [{"name": "TÜMÜ", "bt": allrows}]:
        m = bt_metrics(L["bt"])
        if m:
            out += (f"<tr><td>{e(L['name'])}</td><td class='n'>{m['n']}</td><td class='n'>{pct(m['x2'])}</td>"
                    f"<td class='n'>{pct(m['o25'])}</td><td class='n'>{pct(m['o15'])}</td>"
                    f"<td class='n'>{pct(m['btts'])}</td><td class='n'>{pct(m['p25'])}</td>"
                    f"<td class='n'>{pct(m['r25'])}</td></tr>")
    out += "</table></div>"
    for title, pk, ak in (("2.5 Üst", "o25", "a25"), ("1.5 Üst", "o15", "a15"), ("KG Var", "btts", "abtts")):
        cal = calibration(allrows, pk, ak)
        if not cal:
            continue
        out += f"<h3>Kalibrasyon: {title}</h3><p class='row'>Model %X dediğinde gerçekte kaç kez oldu?</p>"
        out += "<table><tr><th>Tahmin aralığı</th><th class='n'>Maç</th><th class='n'>Ort. tahmin</th><th class='n'>Gerçekleşen</th></tr>"
        for lo, hi, n, mp, ar in cal:
            out += (f"<tr><td>{lo * 100:.0f}-{min(hi, 1) * 100:.0f}%</td><td class='n'>{n}</td>"
                    f"<td class='n'>{pct(mp)}</td><td class='n'>{pct(ar)}</td></tr>")
        out += "</table>"
    return out


def write_html(leagues, now):
    e = html.escape
    local = now.astimezone(TR)
    nav = ["<button data-t='ozet' class='on'>Özet</button>"]
    tabs = [f"<section class='tab on' id='ozet'>{summary_tab(leagues)}</section>"]
    for i, L in enumerate(leagues):
        tid = f"l{i}"
        nav.append(f"<button data-t='{tid}'>{e(L['name'])} <small>{len(L['cards'])}</small></button>")
        if L["err"]:
            body = f"<p class='err'>{e(L['err'])}</p>"
        elif not L["cards"]:
            body = "<p class='empty'>Bugün bu ligde maç yok.</p>"
        else:
            body = "".join(card_html(c) for c in L["cards"])
        a90 = f" · son 90 gün maç başı {L['avg90']:.2f} gol" if L["avg90"] else ""
        tabs.append(f"<section class='tab' id='{tid}'><h2>{e(L['name'])}</h2>"
                    f"<p class='row'>{L['nfin']} geçmiş maç verisi{a90}</p>{body}</section>")
    nav.append("<button data-t='dogruluk'>Doğruluk</button>")
    tabs.append(f"<section class='tab' id='dogruluk'>{accuracy_tab(leagues)}</section>")

    page = (f"<!doctype html><html lang='tr'><head><meta charset='utf-8'>"
            f"<meta name='viewport' content='width=device-width, initial-scale=1'>"
            f"<title>Günün Maçları</title><style>{CSS}</style></head><body>"
            f"<header><h1>Günün Maçları</h1><div class='upd'>Güncelleme: "
            f"{local:%d.%m.%Y %H:%M} · Model tahmindir, kâr garantisi vermez.</div></header>"
            f"<nav>{''.join(nav)}</nav>{''.join(tabs)}<script>{JS}</script></body></html>")
    with open("index.html", "w", encoding="utf-8") as f:
        f.write(page)


if __name__ == "__main__":
    main()
