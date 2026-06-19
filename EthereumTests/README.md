# Native backend build placeholder

EVMYul's FFI library checks for this directory relative to the parent package
before attempting to initialize its own optional EthereumTests submodule.
Keeping the directory here prevents executable builds from running an unrelated
submodule command in this repository. No conformance fixtures are vendored here.
