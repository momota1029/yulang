import { defineConfig } from "vite";

export default defineConfig({
  base: "/yulang/",
  build: {
    target: "es2022",
    outDir: "../dist",
    emptyOutDir: true,
  },
});
