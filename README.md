# Ramanujan in Lean

ラマヌジャンが残した数学的結果を Lean 4 で形式化し、機械で検証するプロジェクトです。計画の全文は [docs/proposal.md](docs/proposal.md) にあります。

## いまの状態

| ID | 内容 | 状態 |
|---|---|---|
| B3.16.22.iii | f(-q) = (q;q)_∞ | proved（意味の監査は match。原本での確認待ち） |
| B3.16.19 | Jacobi の三重積 | registered |
| B3.16.22.i | φ(q) の積表示 | registered |
| B3.16.22.ii | ψ(q) の積表示 | registered |

## 構成

| 場所 | 中身 |
|---|---|
| `RamanujanLean/Defs/` | 共通の定義。Ramanujan の一般テータ関数 f(a,b) など |
| `RamanujanLean/Berndt/Part<n>/Ch<m>/` | Berndt の巻・章ごとの定理 |
| `data/entries/<ID>.toml` | 台帳の正本。1つの結果につき1ファイル |
| `scripts/ledger.py` | 台帳を検査し、`data/ledger.db`（SQLite）を生成する |
| `.github/workflows/ci.yml` | ビルド、公理の監査、台帳の検査 |

台帳の ID、状態、品質の決まりは [docs/ledger.md](docs/ledger.md) に書いてあります。

## 手元での検証

```bash
lake exe cache get              # Mathlib のビルド済みファイルを取る
lake build RamanujanLean
uv run scripts/ledger.py build  # 台帳の検査と data/ledger.db の生成
```

公理の監査は CI で [axiom-audit](https://github.com/leanprover-community/axiom-audit) が行います。手元で走らせるときは、axiom-audit を clone して `lean-toolchain` を `leanprover/lean4:v4.28.0` に書き換え、`lake build` した実行ファイルをこのリポジトリで `lake env <path>/axiom-audit` として呼びます。

## 依存

- Lean 4 v4.28.0、Mathlib v4.28.0
- [invitation-to-qseries-lean](https://github.com/xiangyazi24/invitation-to-qseries-lean)（Apache-2.0、Formally Correct）。Hei-Chi Chan『An Invitation to q-Series』の形式化です。Mathlib の版はこのリポジトリに合わせています。lake の依存として参照し、ファイルは複製していません。

## 原典の扱い

TIFR はノートの全巻の著作権を持つと表明しているため、原典の画像はこのリポジトリに置きません。台帳には Berndt の巻・章・Entry 番号とページ番号だけを記録します。
