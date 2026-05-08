<script setup lang="ts">
import DefaultTheme from "vitepress/theme";

const { Layout } = DefaultTheme;
</script>

<template>
  <Layout>
    <template #nav-bar-content-after>
      <a class="external-nav-link" href="/yulang/" target="_self">Playground</a>
    </template>
  </Layout>
</template>

<style scoped>
.external-nav-link {
  display: inline-flex;
  align-items: center;
  margin: 0 12px;
  padding: 0 4px;
  font-size: 14px;
  font-weight: 500;
  color: var(--vp-c-text-1);
  text-decoration: none;
  transition: color 0.25s;
}
.external-nav-link:hover {
  color: var(--vp-c-brand-1);
}
</style>
