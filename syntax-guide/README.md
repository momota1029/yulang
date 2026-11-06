# Yulang 構文ガイド

Yulang を**書く人**に向けて、構文を最初から最後まで説明する文書。
意味の仕様は `spec/`、構文木(CST)の配置は `syntax-reference/` が正本で、このガイドは「どう読まれるか」を説明する。

- `ja/` が日本語版(最初に書く)。
- 例のコードは、パーサ(`crates/yu-syntax`)に通して検査する予定(`ja/src/checking.md`)。検査が済むまでは「未検査」と書く。
- 構文が確定していない所は「仮採用」と書く。

mdBook で読む:

```text
cd syntax-guide/ja && mdbook serve
```
