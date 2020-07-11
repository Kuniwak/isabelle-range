Proof Drive Development Example
===============================

このサンプルは「[整数の閉区間](https://gist.github.com/twada/75fb219c8cc180e9de166d8a58e877b0)」に基づくものです。



Specifications
--------------

| 仕様番号 | 実装状況 | 仕様 |
|:---------|:---------|:-----|
| NLS-1    | X        | 整数閉区間を示すクラス（あるいは構造体）をつくりたい。 |
| NLS-2    | X        | 整数閉区間オブジェクトは下端点と上端点を持ち、 |
| NLS-3    | X        | 文字列表現も返せる |
| NLS-4    | X        | （例: 下端点 3, 上端点 8 の整数閉区間の文字列表記は `"[3,8]"`）。 |
| NLS-5    | X        | ただし、上端点より下端点が大きい閉区間を作ることはできない。 |
| NLS-6    | X        | 整数の閉区間は指定した整数を含むかどうかを判定できる。 |
| NLS-7    | X        | また、別の閉区間と等価かどうかや、 |
| NLS-8    | X        | 完全に含まれるかどうかも判定できる。 |
| NLS-9    | X        | 例: 閉区間 `[3,8]` の場合`[3,8]` |
| NLS-10   | X        | → 下端点 (lower endpoint) が 3 , 上端点 (upper endpoint) が 8 である整数閉区間 |
| NLS-11   | X        | → 3 と 8 は区間に含まれる |
| NLS-12   | X        | → つまり (整数閉区間だから) 3,4,5,6,7,8 |
