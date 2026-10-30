import math
def pois(l, n=11): 
    return [math.exp(-l) * l**k / math.factorial(k) for k in range(n)]
def probs(lh, la, h1, a1):
    """İki yarıyı bağımsız Poisson sayar: İY (h1,a1), 2. yarı (lh-h1, la-a1)."""
    h2, a2 = max(lh - h1, 0.01), max(la - a1, 0.01)
    P1h, P1a, P2h, P2a = pois(h1), pois(a1), pois(h2), pois(a2)
    out = {}
    def add(k, v): out[k] = out.get(k, 0) + v
    for i, pi in enumerate(P1h):
        for j, pj in enumerate(P1a):
            q1 = pi * pj
            if q1 < 1e-7: continue
            for k, pk in enumerate(P2h):
                for l, pl in enumerate(P2a):
                    q = q1 * pk * pl
                    if q < 1e-9: continue
                    H, A = i + k, j + l
                    ht = "1" if i > j else ("X" if i == j else "2")
                    ft = "1" if H > A else ("X" if H == A else "2")
                    add("htft_" + ht + "/" + ft, q)
                    add(f"cs_{H}-{A}" if H <= 4 and A <= 4 else "cs_other", q)
                    if i > 0 and j > 0: add("iykg", q)
                    if H + A >= 6: add("o55", q)
                    if H + A >= 5: add("o45", q)
                    if i + j >= 2: add("iy15", q)
                    if i + j >= 2 and H + A >= 3: add("iy15_o25", q)
                    if i + j >= 1 and H + A >= 3: add("iy05_o25", q)
                    if k + l >= 2: add("y2_15", q)                 # 2. yarı 1.5 üst
                    if i + j >= 2 and k + l >= 2: add("iki_yari_15", q)  # iki yarıda da 1.5 üst
                    if H > 0 and A > 0 and H + A >= 3: add("kg_o25", q)
                    if H > A and H + A >= 3: add("ms1_o25", q)
                    if A > H and H + A >= 3: add("ms2_o25", q)
                    if i + j >= 1 and k + l >= 1: add("iki_yari_gol", q)
    return out
def actual(hg, ag, ht):
    i, j = ht; k, l = hg - i, ag - j
    a = {}
    hts = "1" if i > j else ("X" if i == j else "2"); fts = "1" if hg > ag else ("X" if hg == ag else "2")
    for x in "1X2":
        for y in "1X2": a[f"htft_{x}/{y}"] = (hts, fts) == (x, y)
    for H in range(5):
        for A in range(5): a[f"cs_{H}-{A}"] = (hg, ag) == (H, A)
    a["cs_other"] = hg > 4 or ag > 4
    a.update(iykg=i > 0 and j > 0, o55=hg + ag >= 6, o45=hg + ag >= 5, iy15=i + j >= 2, iy15_o25=i + j >= 2 and hg + ag >= 3,
             iy05_o25=i + j >= 1 and hg + ag >= 3, y2_15=k + l >= 2, iki_yari_15=i + j >= 2 and k + l >= 2,
             kg_o25=hg > 0 and ag > 0 and hg + ag >= 3, ms1_o25=hg > ag and hg + ag >= 3, ms2_o25=ag > hg and hg + ag >= 3,
             iki_yari_gol=i + j >= 1 and k + l >= 1)
    return a


# ---- Düzeltilmiş ihtimal: geçmiş 2.509 maçta (bot.py geriye dönük testi) modelin her pazarda ne kadar
# iyimser/kötümser olduğu ondalık dilimlerle ölçüldü (data/surp_cal.json). Kupon kurarken ham değil bunu kullan.
import json as _json, os as _os
_CAL = _json.load(open(_os.path.join(_os.path.dirname(__file__), "..", "data", "surp_cal.json")))


def adj(k, p):
    pts = _CAL[k]; xs = [x for x, _ in pts]
    if p >= xs[-1]:
        return min(pts[-1][1] * p / xs[-1], pts[-1][1] + 0.08)
    for (x0, y0), (x1, y1) in zip(pts, pts[1:]):
        if x0 <= p <= x1:
            return y0 + (y1 - y0) * (p - x0) / (x1 - x0) if x1 > x0 else y0
    return pts[0][1]


def match_probs(entry):
    """analiz.json / plan.json maç kaydı -> {pazar: (düzeltilmiş, ham)}; "l" = [ev, dep, ev İY, dep İY] gol beklentisi."""
    raw = probs(*entry["l"])
    return {k: (adj(k, v), v) for k, v in raw.items() if k in _CAL}
# Bahis kodları (bet_settle ile sonuçlanır): htft_1/1 -> im11, htft_2/2 -> im22, htft_X/1 -> imx1, htft_X/2 -> imx2,
# ms1_o25 -> ms1+o25, ms2_o25 -> ms2+o25, kg_o25 -> kgv+o25, o45 -> o45, o55 -> o55, iykg -> iykgv, iy15 -> iyo15,
# cs_2-1 -> sk2-1. Geçmiş testte modelin HİÇ bilemediği pazarlar: htft_2/1, htft_1/2 (geri dönüşler), doğru skor (zayıf),
# iy15 ve iykg en üst dilimde çok iyimser.
