# 台帳の決まり

## ID

Berndt『Ramanujan's Notebooks』Part I〜V の番号から作ります。

```
B<巻>.<章>.<Entry>[.<小項目>]
```

例として、Part III 第16章 Entry 22(iii) は `B3.16.22.iii` です。小項目はローマ数字の小文字で書きます。

失われたノート（Andrews–Berndt『Ramanujan's Lost Notebook』）、論文、書簡の ID は、まだ決めていません。

## 状態

| 状態 | 条件 |
|---|---|
| registered | 原典の位置と LaTeX の命題を登録した |
| formalized | Lean の命題を書いた。証明はまだない |
| proved | Lean の証明が通り、axiom-audit と台帳の検査を通った |
| verified | proved に加え、書き手と別の監査者が原典との意味の一致を確かめ、原本で式を確かめた（`original_checked = true`） |
| rejected | 原典の誤記、または成り立たない命題と判断した。理由を notes に書く |

`scripts/ledger.py` は、proved と verified の項目について次を確かめます。

- `[lean].theorems` に書いた定理がすべて存在する
- その定理が propext、Classical.choice、Quot.sound 以外の公理を使っていない
- verified の項目は `semantic_audit.verdict = "match"` で、監査者が書き手と別であり、`source.original_checked = true` である

## 品質の決まり

- `sorry`、`admit`、`native_decide`、独自の `axiom` は使いません。CI の axiom-audit が `RamanujanLean` 名前空間の全宣言を検査し、依存先から入ったものも止めます。
- 級数と無限積の等式は `HasSum` と `HasProd` で書きます。`tsum` と `tprod` は収束しないときに 0 と 1 を返すため、それだけの等式では収束しない場合も成り立ってしまいます。
- 原典にない仮定は足しません。足すときは `[lean].formulation_notes` に理由を書きます。
- 形式的冪級数の等式は、原典が複素数 q の等式なら解析版と別の命題として扱います。形式版だけ通した項目は verified にしません。

## 意味の監査で確かめること

1. Lean の命題が原典の式と同じことを主張しているか。定義域、収束条件、添字の範囲、符号の約束が合っているか
2. 仮定が原典より強くなっていないか。仮定が矛盾していて、何でも証明できる状態になっていないか
3. 原典の式を、証明しやすい別の式に書き換えていないか

結果は `[semantic_audit]` の verdict、reviewer、notes に書きます。
