import { defineConfig } from "vitepress";
import yulangGrammar from "./yulang-grammar";

export default defineConfig({
  title: "Yulang",
  description:
    "A statically-typed language with algebraic effects and role-based polymorphism.",
  lang: "en",

  base: "/docs/",
  outDir: "../dist/docs",

  ignoreDeadLinks: [/^\/playground\//],

  markdown: {
    languages: [yulangGrammar],
  },

  themeConfig: {
    logo: undefined,

    nav: [
      { text: "Guide", link: "/guide/" },
      { text: "Reference", link: "/reference/" },
    ],

    sidebar: {
      "/guide/": [
        {
          text: "Guide",
          items: [
            { text: "Introduction", link: "/guide/" },
            { text: "Tour", link: "/guide/tour" },
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
            { text: "Application & Operators", link: "/reference/application" },
            { text: "Structs & Roles", link: "/reference/structs" },
            { text: "Effects", link: "/reference/effects" },
            { text: "Pattern Matching", link: "/reference/patterns" },
            { text: "Modules", link: "/reference/modules" },
          ],
        },
        {
          text: "Standard Library",
          items: [{ text: "std::undet", link: "/reference/std/undet" }],
        },
      ],
    },

    socialLinks: [],

    footer: {
      message: "Yulang",
    },
  },
});
