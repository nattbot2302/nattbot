import os
import time
import math
import html
import datetime as dt
import requests

API = "https://api.football-data.org/v4"
KEY = os.environ["FOOTBALL_API_KEY"]
HEADERS = {"X-Auth-Token": KEY}

# Takip edilen ligler (football-data.org kodları). Sonra buradan değiştiririz.
LEAGUES = ["PL", "PD", "SA", "BL1", "FL1"]
TR = dt.timezone(dt.timedelta(hours=3))


def get(path, params=None):
    for _ in range(4):
        r = requests.get(API + path, headers=HEADERS, params=params, timeout=30)
        if r.status_code == 429:  # dakikalık limit
            time.sleep(65)
            continue
        r.raise_for_status()
        time.sleep(7)  # ücretsiz limit: dakikada 10 istek
        return r.json()
    raise RuntimeError("API limiti aşıldı")


def pois(k, lam):
    return math.exp(-lam) * lam ** k / math.factorial(k)


def shrink(values, prior, k=3):
    # Az maçı olan takımlarda lig ortalamasına doğru yumuşatma
    return (sum(values) + prior * k) / (len(values) + k)


def build_stats(matches):
    teams = {}
    hg, ag = [], []
    for m in matches:
        s = m["score"]["fullTime"]
        if s["home"] is None or s["away"] is None:
            continue
        h, a = m["homeTeam"]["id"], m["awayTeam"]["id"]
        for t in (h, a):
            teams.setdefault(t, {"hf": [], "ha": [], "af": [], "aa": []})
        teams[h]["hf"].append(s["home"])
        teams[h]["ha"].append(s["away"])
        teams[a]["af"].append(s["away"])
        teams[a]["aa"].append(s["home"])
        hg.append(s["home"])
        ag.append(s["away"])
    if not hg:
        return None
    return {"teams": teams, "lg_h": sum(hg) / len(hg), "lg_a": sum(ag) / len(ag)}


def lambdas(stats, h, a):
    T, lh, la = stats["teams"], stats["lg_h"], stats["lg_a"]
    if h not in T or a not in T:
        return None
    att_h = shrink(T[h]["hf"], lh) / lh
    def_a = shrink(T[a]["aa"], lh) / lh
    att_a = shrink(T[a]["af"], la) / la
    def_h = shrink(T[h]["ha"], la) / la
    return lh * att_h * def_a, la * att_a * def_h


def analyze(lam_h, lam_a, n=9):
    grid = {(i, j): pois(i, lam_h) * pois(j, lam_a) for i in range(n) for j in range(n)}
    p1 = sum(p for (i, j), p in grid.items() if i > j)
    px = sum(p for (i, j), p in grid.items() if i == j)
    p2 = sum(p for (i, j), p in grid.items() if i < j)
    o15 = sum(p for (i, j), p in grid.items() if i + j >= 2)
    o25 = sum(p for (i, j), p in grid.items() if i + j >= 3)
    btts = sum(p for (i, j), p in grid.items() if i >= 1 and j >= 1)
    top = sorted(grid.items(), key=lambda x: -x[1])[:3]
    return {"p1": p1, "px": px, "p2": p2, "o15": o15, "o25": o25, "btts": btts,
            "top": [(f"{i}-{j}", p) for (i, j), p in top]}


def similar(stats, matches, lam_h, lam_a, k=3):
    scored = []
    for m in matches:
        s = m["score"]["fullTime"]
        if s["home"] is None:
            continue
        lam = lambdas(stats, m["homeTeam"]["id"], m["awayTeam"]["id"])
        if not lam:
            continue
        d = (lam[0] - lam_h) ** 2 + (lam[1] - lam_a) ** 2
        scored.append((d, m))
    scored.sort(key=lambda x: x[0])
    out = []
    for _, m in scored[:k]:
        s = m["score"]["fullTime"]
        out.append(f"{m['utcDate'][:10]} {m['homeTeam']['shortName']} "
                   f"{s['home']}-{s['away']} {m['awayTeam']['shortName']}")
    return out


def season_start(today):
    return today.year if today.month >= 8 else today.year - 1


def pct(x):
    return f"{x * 100:.0f}%"


def cls(x):
    return "hi" if x >= 0.6 else ("mid" if x >= 0.45 else "lo")


def main():
    now = dt.datetime.now(TR)
    today = now.date().isoformat()
    data = get("/matches", {"dateFrom": today, "dateTo": today})
    todays = [m for m in data.get("matches", []) if m["competition"]["code"] in LEAGUES]

    codes = sorted({m["competition"]["code"] for m in todays})
    cards = []
    for code in codes:
        finished = []
        for season in (season_start(now.date()), season_start(now.date()) - 1):
            try:
                res = get(f"/competitions/{code}/matches",
                          {"season": season, "status": "FINISHED"})
                finished += res.get("matches", [])
            except Exception as e:
                print("Veri alınamadı", code, season, e)
        stats = build_stats(finished)
        if not stats:
            continue
        for m in [x for x in todays if x["competition"]["code"] == code]:
            lam = lambdas(stats, m["homeTeam"]["id"], m["awayTeam"]["id"])
            if not lam:
                continue
            r = analyze(*lam)
            kick = dt.datetime.fromisoformat(m["utcDate"].replace("Z", "+00:00")).astimezone(TR)
            cards.append({
                "league": m["competition"]["name"],
                "time": kick.strftime("%H:%M"),
                "home": m["homeTeam"]["shortName"] or m["homeTeam"]["name"],
                "away": m["awayTeam"]["shortName"] or m["awayTeam"]["name"],
                "lam": lam, "r": r,
                "sim": similar(stats, finished, *lam),
            })
    cards.sort(key=lambda c: c["time"])
    write_html(cards, now)


def write_html(cards, now):
    e = html.escape
    body = ""
    for c in cards:
        r = c["r"]
        sim = "".join(f"<li>{e(s)}</li>" for s in c["sim"])
        top = ", ".join(f"{s} ({pct(p)})" for s, p in c["top"])
        body += f"""
<div class="card">
  <div class="meta">{e(c['league'])} · {c['time']}</div>
  <h2>{e(c['home'])} - {e(c['away'])}</h2>
  <div class="grid">
    <div class="b {cls(r['o15'])}">1.5 Üst<br><b>{pct(r['o15'])}</b></div>
    <div class="b {cls(r['o25'])}">2.5 Üst<br><b>{pct(r['o25'])}</b></div>
    <div class="b {cls(r['btts'])}">KG Var<br><b>{pct(r['btts'])}</b></div>
  </div>
  <div class="row">MS1 {pct(r['p1'])} · MSX {pct(r['px'])} · MS2 {pct(r['p2'])}</div>
  <div class="row">Beklenen gol: {c['lam'][0]:.2f} - {c['lam'][1]:.2f}</div>
  <div class="row">Olası skorlar: {top}</div>
  <details><summary>Benzer geçmiş maçlar</summary><ul>{sim}</ul></details>
</div>"""
    if not body:
        body = '<p class="empty">Bugün takip edilen liglerde maç yok.</p>'
    page = f"""<!doctype html>
<html lang="tr"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Günün Maçları</title>
<style>
:root{{--bg:#f4f5f7;--card:#fff;--tx:#1a1a1a;--mu:#666;--hi:#c8f0d2;--mid:#fdf0c4;--lo:#eee}}
@media (prefers-color-scheme:dark){{:root{{--bg:#111;--card:#1c1c1e;--tx:#eee;--mu:#999;--hi:#1f5130;--mid:#5a4a14;--lo:#2a2a2c}}}}
body{{margin:0;padding:12px;background:var(--bg);color:var(--tx);font-family:system-ui,sans-serif}}
h1{{font-size:20px}} h2{{font-size:17px;margin:4px 0 10px}}
.card{{background:var(--card);border-radius:12px;padding:14px;margin-bottom:12px}}
.meta,.row,.upd{{color:var(--mu);font-size:13px;margin-top:6px}}
.grid{{display:grid;grid-template-columns:repeat(3,1fr);gap:8px}}
.b{{text-align:center;border-radius:8px;padding:8px 4px;font-size:13px}}
.b b{{font-size:18px}} .hi{{background:var(--hi)}} .mid{{background:var(--mid)}} .lo{{background:var(--lo)}}
summary{{margin-top:8px;font-size:13px}} li{{font-size:13px;color:var(--mu)}}
</style></head><body>
<h1>Günün Maçları</h1>
<div class="upd">Güncelleme: {now.strftime('%d.%m.%Y %H:%M')} · Model tahmindir, kâr garantisi vermez.</div>
{body}
</body></html>"""
    with open("index.html", "w", encoding="utf-8") as f:
        f.write(page)


if __name__ == "__main__":

main()
