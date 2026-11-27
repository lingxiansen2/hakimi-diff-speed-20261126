import { join } from 'node:path';
import { setFlagsFromString } from 'node:v8';

setFlagsFromString('--no-incremental-marking');
setFlagsFromString('--no-concurrent-recompilation');
setFlagsFromString('--liftoff-only');

const { runCasesFile } = (await import(new URL('./solve.js', import.meta.url).href)) as {
  runCasesFile: (inputPath: string, outputPath: string) => void;
};

const INPUT_DIR = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUTPUT_DIR = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

runCasesFile(join(INPUT_DIR, 'cases.json'), join(OUTPUT_DIR, 'answers.json'));
