import { defineConfig } from "vitepress";
import yulangGrammar from "./yulang-grammar";

const englishNav = [
  { text: "Guide", link: "/guide/" },
  { text: "Reference", link: "/reference/" },
];

const japaneseNav = [
  { text: "ガイド", link: "/ja/guide/" },
  { text: "リファレンス", link: "/ja/reference/" },
];

const englishSidebar = {
  "/guide/": [
    {
      text: "Guide",
      items: [
        { text: "Introduction", link: "/guide/" },
        { text: "Tour", link: "/guide/tour" },
        { text: "Cookbook", link: "/guide/cookbook" },
        { text: "Cheat Sheet", link: "/guide/cheat-sheet" },
        { text: "Pitfalls", link: "/guide/pitfalls" },
        { text: "Installation", link: "/guide/install" },
      ],
    },
  ],
  "/reference/": [
    {
      text: "Language Reference",
      items: [
        { text: "Overview", link: "/reference/" },
        { text: "Values & Types", link: "/reference/types" },
        { text: "Functions", link: "/reference/functions" },
        { text: "Control Flow", link: "/reference/control-flow" },
        { text: "Strings", link: "/reference/strings" },
        { text: "Application & Operators", link: "/reference/application" },
        { text: "Syntax Style", link: "/reference/syntax-style" },
        { text: "Operator Declarations", link: "/reference/operators" },
        { text: "Structs & Roles", link: "/reference/structs" },
        { text: "Casts", link: "/reference/casts" },
        { text: "Effects", link: "/reference/effects" },
        { text: "Errors", link: "/reference/errors" },
        { text: "Pattern Matching", link: "/reference/patterns" },
        { text: "Modules", link: "/reference/modules" },
        { text: "Idioms", link: "/reference/idioms" },
      ],
    },
    {
      text: "Standard Library",
      items: [
        { text: "Core Std", link: "/reference/std/core" },
        { text: "std::list", link: "/reference/std/list" },
        { text: "std::str", link: "/reference/std/str" },
        { text: "std::opt", link: "/reference/std/opt" },
        { text: "std::result", link: "/reference/std/result" },
        { text: "std::undet", link: "/reference/std/undet" },
      ],
    },
  ],
};

const japaneseSidebar = {
  "/ja/guide/": [
    {
      text: "ガイド",
      items: [
        { text: "はじめに", link: "/ja/guide/" },
        { text: "ツアー", link: "/ja/guide/tour" },
        { text: "クックブック", link: "/ja/guide/cookbook" },
        { text: "チートシート", link: "/ja/guide/cheat-sheet" },
        { text: "落とし穴", link: "/ja/guide/pitfalls" },
        { text: "インストール", link: "/ja/guide/install" },
      ],
    },
  ],
  "/ja/reference/": [
    {
      text: "言語リファレンス",
      items: [
        { text: "概要", link: "/ja/reference/" },
        { text: "値と型", link: "/ja/reference/types" },
        { text: "関数", link: "/ja/reference/functions" },
        { text: "制御構文", link: "/ja/reference/control-flow" },
        { text: "文字列", link: "/ja/reference/strings" },
        { text: "適用と演算子", link: "/ja/reference/application" },
        { text: "構文スタイル", link: "/ja/reference/syntax-style" },
        { text: "演算子宣言", link: "/ja/reference/operators" },
        { text: "構造体とロール", link: "/ja/reference/structs" },
        { text: "キャスト", link: "/ja/reference/casts" },
        { text: "エフェクト", link: "/ja/reference/effects" },
        { text: "エラー", link: "/ja/reference/errors" },
        { text: "パターンマッチ", link: "/ja/reference/patterns" },
        { text: "モジュール", link: "/ja/reference/modules" },
        { text: "イディオム", link: "/ja/reference/idioms" },
      ],
    },
    {
      text: "標準ライブラリ",
      items: [
        { text: "標準ライブラリ中核", link: "/ja/reference/std/core" },
        { text: "std::list", link: "/ja/reference/std/list" },
        { text: "std::str", link: "/ja/reference/std/str" },
        { text: "std::opt", link: "/ja/reference/std/opt" },
        { text: "std::result", link: "/ja/reference/std/result" },
        { text: "std::undet", link: "/ja/reference/std/undet" },
      ],
    },
  ],
};

export default defineConfig({
  title: "Yulang",
  description:
    "A statically-typed language with algebraic effects and role-based polymorphism.",
  lang: "en",

  base: "/",
  outDir: "../dist-docs",
  appearance: true,

  ignoreDeadLinks: [/^\/playground\//],

  markdown: {
    languages: [yulangGrammar],
  },

  locales: {
    root: {
      label: "English",
      lang: "en",
      title: "Yulang",
      description:
        "A statically-typed language with algebraic effects and role-based polymorphism.",
    },
    ja: {
      label: "日本語",
      lang: "ja",
      title: "Yulang",
      description:
        "代数的エフェクトとロールベース多相を持つ静的型付き言語。",
      themeConfig: {
        logoLink: "/ja/guide/",
        nav: japaneseNav,
        sidebar: japaneseSidebar,
      },
    },
  },

  themeConfig: {
    logo: undefined,
    logoLink: "/guide/",

    nav: englishNav,

    sidebar: englishSidebar,

    socialLinks: [],

    footer: {
      message: "Yulang",
    },
  },
});
