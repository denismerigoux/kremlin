## Compatibility libraries

These are intended tofacilitate porting old code written using `FStar.Buffer`.
In particular, we wish to enable a "hybrid" build where old code and new code
can happily co-exist. In order to achieve this:
- `kremlib/` should have precedence over `kremlib/compat` (watch out for the
  semantics of `--include` in F\*!)
- `C.Endianness`, in old code, should be used via `C.Compat.Endianness` which
  will ensure that old code continues to see endianness functions that rely on
  `FStar.Buffer`.
- `C.Loops`, in old code, should be used via `C.Compat.Loops`
- `Spec.Loops`, in old code, should be used via `Spec.Compat.Loops`
