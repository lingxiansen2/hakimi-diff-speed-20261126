const { createRequire } = process.getBuiltinModule('node:module');
const engine = createRequire(import.meta.url)('./engine.cjs');

export const FORMAT = engine.FORMAT;
export const CONTEXT = engine.CONTEXT;
export const diffPatch = engine.diffPatch;
export const run = engine.run;
export const runCasesFile = engine.runCasesFile;
