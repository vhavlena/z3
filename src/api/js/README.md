# TypeScript Bindings

This directory contains JavaScript code to automatically derive TypeScript bindings for the C API, which are published on npm as [z3-solver](https://www.npmjs.com/package/z3-solver).

The readme for the bindings themselves is located in [`PUBLISHED_README.md`](./PUBLISHED_README.md).


## Building

You'll need to have emscripten set up, along with all of its dependencies. The easiest way to do that is with [emsdk](https://github.com/emscripten-core/emsdk). Newer versions of emscripten may break the build; you can find the version used in CI in [this file](https://github.com/Z3Prover/z3/blob/master/.github/workflows/wasm.yml#L13).

Then run `npm i` to install dependencies, `npm run build:ts` to build the TypeScript wrapper, and `npm run build:wasm` to build the wasm artifact.

Detailed instruction for binding building for Z3-Noodler:
1) Get emscripten trough [emsdk](https://github.com/emscripten-core/emsdk) and activate its environment:
    ```shell
    git clone 'https://github.com/emscripten-core/emsdk'
    cd emdsk
    ./emsdk install 3.1.73
    ./emsdk activate 3.1.73
    source emsdk_env.sh
    cd ..
    ```
2) Get and install [Mata](https://github.com/VeriFIT/mata/) library (it will be installed into `emsdk` environment, so no need `sudo` or a worry if `mata` is already installed):
    ```shell
    git clone 'https://github.com/VeriFIT/mata.git'
    cd mata
    mkdir build && cd build
    emcmake cmake -DCMAKE_BUILD_TYPE=Release -DMATA_BUILD_EXAMPLES:BOOL=OFF -DBUILD_TESTING:BOOL=OFF ..
    emmake make install
    cd ..
    ```
3) Find the line on the installation output that contains the path to `libmata.a` and copy it onto line 77 of `scripts/build-wasm.ts`
4) Create an empty `build` directory in the root of `z3-noodler` directory.
5) Run the following commands while in this directory (where this readme is) to build the binding:
    ```shell
    npm install
    npm run build:ts
    npm run build:wasm
    ```
6) You can add dependency to this binding by adding the following to your `package.json` file:
    ```
    "dependencies": {
        "z3-solver": "file:PATH/TO/THIS/DIRECTORY"
    }
    ```

### Build on your own

Consult the file [build-wasm.ts](https://github.com/Z3Prover/z3/blob/master/src/api/js/scripts/build-wasm.ts) for configurations used for building wasm.

## Tests

Run `npm test` after building to run tests.
