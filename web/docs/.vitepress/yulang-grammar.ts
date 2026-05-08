import type { LanguageRegistration } from "vitepress";

const grammar: LanguageRegistration = {
  name: "yulang",
  scopeName: "source.yulang",
  fileTypes: ["yu"],
  patterns: [
    { include: "#comment" },
    { include: "#string" },
    { include: "#number" },
    { include: "#keyword" },
    { include: "#type-var" },
    { include: "#operator" },
    { include: "#identifier" },
  ],
  repository: {
    comment: {
      name: "comment.line.yulang",
      match: "--.*$",
    },
    string: {
      name: "string.quoted.double.yulang",
      begin: '"',
      end: '"',
      patterns: [
        { name: "constant.character.escape.yulang", match: "\\\\." },
      ],
    },
    number: {
      name: "constant.numeric.yulang",
      match: "\\b[0-9]+(?:\\.[0-9]+)?\\b",
    },
    keyword: {
      name: "keyword.control.yulang",
      match:
        "\\b(my|our|pub|let|in|if|else|match|struct|with|act|catch|role|impl|for|use|sub|return|guard|some|none|true|false|each|all|any|once|list|every|undet)\\b",
    },
    "type-var": {
      name: "entity.name.type.yulang",
      match: "'[a-z][a-zA-Z0-9_]*",
    },
    operator: {
      name: "keyword.operator.yulang",
      match: "->|=>|::|\\.\\.\\.|\\.\\.|\\.\\.|&&|\\|\\||[+\\-*/%<>=!&|^~]+",
    },
    identifier: {
      patterns: [
        {
          name: "support.function.yulang",
          match: "\\b(println|print)\\b",
        },
        {
          name: "variable.other.yulang",
          match: "\\$[a-z_][a-zA-Z0-9_]*",
        },
        {
          name: "variable.other.mutable.yulang",
          match: "&[a-z_][a-zA-Z0-9_]*",
        },
        {
          name: "entity.name.type.struct.yulang",
          match: "\\b[a-z][a-zA-Z0-9_]*(?=\\s*\\{)",
        },
        {
          name: "variable.other.yulang",
          match: "\\b[a-z_][a-zA-Z0-9_]*\\b",
        },
      ],
    },
  },
};

export default grammar;
