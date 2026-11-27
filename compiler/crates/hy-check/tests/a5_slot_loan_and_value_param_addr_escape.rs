//! Regression tests for A5 Go-escape check-site (`HYB-E3013`, SPEC-LANGUAGE §8.5 C9,
//! GUARANTEES Rows 5 & 9):
//! 1. O8 slot loans (`p := &m["k"]`, `p := &s.sub`, `p := &xs[0]`, `p = &m["k"]`) lower in
//!    `hy-emit` to copy-out plus an unconditional store-back (`m["k"] = p`, `m["k"] = *p`,
//!    `s.sub = p`, `xs[0] = p`), so even read-only O8 slot loans on captured shared state
//!    inside escaping closures or their callees write to the captured container at runtime
//!    and must reject with `HYB-E3013`.
//! 2. Address-of (`p := &h`), pointer-argument calls (`write_ptr(&h)`), and auto-addressed
//!    pointer-receiver method calls (`h.stomp_ptr()`) on value-passed composite parameters
//!    carrying shared interior references (`map`/`slice`/`*T`) must preserve shared-interior
//!    provenance and reject interior mutations with `HYB-E3013`, while keeping mutations of
//!    local scalar/sub-struct/fixed-array value copies accepted.

use hy_check::{check_file, Verdict};
use hy_syntax::parse_file;

fn check(src: &str) -> hy_check::CheckResult {
    let ast = parse_file("a5_slot_loan_escape.hy", src).expect("snippet must parse");
    check_file(&ast)
}

fn error_codes(r: &hy_check::CheckResult) -> Vec<&str> {
    r.diagnostics
        .iter()
        .filter(|d| d.severity == hy_diag::Severity::Error)
        .map(|d| d.code.as_str())
        .collect()
}

fn assert_rejects_e3013(src: &str) {
    let r = check(src);
    assert_eq!(
        r.verdict,
        Verdict::Reject,
        "expected Reject for:\n{src}\ngot: {:?}",
        r.diagnostics
    );
    assert_eq!(
        error_codes(&r),
        vec!["HYB-E3013"],
        "expected exact [HYB-E3013] for:\n{src}\ngot: {:?}",
        r.diagnostics
    );
}

fn assert_accepts_clean(src: &str) {
    let r = check(src);
    assert_eq!(
        r.verdict,
        Verdict::Accept,
        "expected Accept for:\n{src}\ngot: {:?}",
        r.diagnostics
    );
    assert!(
        error_codes(&r).is_empty(),
        "expected 0 error diagnostics for:\n{src}\ngot: {:?}",
        r.diagnostics
    );
}

#[test]
fn o8_slot_loan_unconditional_store_backs_reject_e3013() {
    for src in [
        // 1. Unconditional O8 map-slot store-back (`m["k"] = p`) inside `mux.handle`
        "import \"net/http\"\n\
         fn main() {\n\
           m := map[string]int{\"k\": 1}\n\
           mux := http.new_serve_mux()\n\
           mux.handle(\"/x\", http.handler(fn() {\n\
             p := &m[\"k\"]\n\
             _ = p\n\
           }))\n\
         }",
        // 2. Read-only field projection (`_ = p.v`) on O8 struct-map slot loan still emits `m["k"] = p`
        "import \"net/http\"\n\
         struct item { v int }\n\
         fn main() {\n\
           m := map[string]item{\"k\": item{v: 1}}\n\
           http.handle_func(\"/x\", fn(w http.response_writer, r *http.request) {\n\
             p := &m[\"k\"]\n\
             _ = p.v\n\
           })\n\
         }",
        // 3. Assign-form (`Stmt::Assign`) O8 map-slot loan (`p = &m["k"]`) onto `*item` emits `m["k"] = *p`
        "import \"net/http\"\n\
         struct item { v int }\n\
         fn main() {\n\
           m := map[string]item{\"k\": item{v: 1}}\n\
           http.handle_func(\"/x\", fn(w http.response_writer, r *http.request) {\n\
             local_item := item{v: 0}\n\
             p := &local_item\n\
             p = &m[\"k\"]\n\
             _ = p.v\n\
           })\n\
         }",
        // 4. O8 struct-field slot loan (`p := &s.sub`) on captured struct emits `s.sub = p`
        "import \"net/http\"\n\
         struct sub { v int }\n\
         struct outer { sub sub }\n\
         fn main() {\n\
           s := outer{sub: sub{v: 1}}\n\
           http.handle_func(\"/x\", fn(w http.response_writer, r *http.request) {\n\
             p := &s.sub\n\
             _ = p.v\n\
           })\n\
           _ = s\n\
         }",
        // 5. O8 slice-element slot loan (`p := &xs[0]`) on captured slice emits `xs[0] = p`
        "import \"net/http\"\n\
         struct item { v int }\n\
         fn main() {\n\
           xs := []item{item{v: 1}}\n\
           http.handle_func(\"/x\", fn(w http.response_writer, r *http.request) {\n\
             p := &xs[0]\n\
             _ = p.v\n\
           })\n\
         }",
        // 6. Helper fn and value-method O8 map-slot loans called from / passed to foreign escape
        "import \"net/http\"\n\
         fn read_map_slot(m map[string]int) {\n\
           p := &m[\"k\"]\n\
           _ = p\n\
         }\n\
         fn main() {\n\
           m := map[string]int{\"k\": 1}\n\
           http.handle_func(\"/x\", fn(w http.response_writer, r *http.request) {\n\
             read_map_slot(m)\n\
           })\n\
         }",
        "import \"net/http\"\n\
         struct holder { m map[string]int }\n\
         fn (h holder) read_slot(w http.response_writer, r *http.request) {\n\
           p := &h.m[\"k\"]\n\
           _ = p\n\
         }\n\
         fn main() {\n\
           h := holder{m: map[string]int{\"k\": 1}}\n\
           http.handle_func(\"/x\", h.read_slot)\n\
           _ = h\n\
         }",
    ] {
        assert_rejects_e3013(src);
    }
}

#[test]
fn value_passed_composite_addr_and_ptr_receiver_interior_mutations_reject_e3013() {
    for src in [
        // 1. Local `&h` on value parameter mutating shared map field
        "import \"net/http\"\n\
         struct holder { m map[string]int\n n int }\n\
         fn sneak_addr(h holder) {\n\
           p := &h\n\
           p.m[\"k\"] = 99\n\
         }\n\
         fn main() {\n\
           h := holder{m: map[string]int{\"k\": 1}, n: 0}\n\
           http.handle_func(\"/x\", fn(w http.response_writer, r *http.request) {\n\
             sneak_addr(h)\n\
           })\n\
           _ = h\n\
         }",
        // 2. Local `&h` on value parameter calling `delete(p.m, "k")`
        "import \"net/http\"\n\
         struct holder { m map[string]int }\n\
         fn sneak_del(h holder) {\n\
           p := &h\n\
           delete(p.m, \"k\")\n\
         }\n\
         fn main() {\n\
           h := holder{m: map[string]int{\"k\": 1}}\n\
           http.handle_func(\"/x\", fn(w http.response_writer, r *http.request) {\n\
             sneak_del(h)\n\
           })\n\
           _ = h\n\
         }",
        // 3. Passing `&h` from value parameter to `*holder` helper that mutates shared map
        "import \"net/http\"\n\
         struct holder { m map[string]int }\n\
         fn write_ptr(p *holder) { p.m[\"k\"] = 99 }\n\
         fn sneak_ptr_call(h holder) { write_ptr(&h) }\n\
         fn main() {\n\
           h := holder{m: map[string]int{\"k\": 1}}\n\
           http.handle_func(\"/x\", fn(w http.response_writer, r *http.request) {\n\
             sneak_ptr_call(h)\n\
           })\n\
           _ = h\n\
         }",
        // 4. Auto-addressed pointer-receiver method `h.stomp_ptr()` on value parameter
        "import \"net/http\"\n\
         struct holder { m map[string]int }\n\
         fn (h *holder) stomp_ptr() { h.m[\"k\"] = 99 }\n\
         fn sneak_ptr_recv(h holder) { h.stomp_ptr() }\n\
         fn main() {\n\
           h := holder{m: map[string]int{\"k\": 1}}\n\
           http.handle_func(\"/x\", fn(w http.response_writer, r *http.request) {\n\
             sneak_ptr_recv(h)\n\
           })\n\
           _ = h\n\
         }",
    ] {
        assert_rejects_e3013(src);
    }
}

#[test]
fn closure_local_slot_loans_and_value_copy_scalar_mutations_stay_accepted() {
    for src in [
        // 1. Closure-local map O8 slot loan does not escape
        "import \"net/http\"\n\
         struct item { v int }\n\
         fn main() {\n\
           http.handle_func(\"/x\", fn(w http.response_writer, r *http.request) {\n\
             m := map[string]item{\"k\": item{v: 1}}\n\
             p := &m[\"k\"]\n\
             p.v = 2\n\
           })\n\
         }",
        // 2. Read-only pointer (`var p *stats = &s`) does not emit an O8 store-back
        "import \"net/http\"\n\
         struct stats { n int }\n\
         fn main() {\n\
           s := stats{n: 1}\n\
           http.handle_func(\"/x\", fn(w http.response_writer, r *http.request) {\n\
             var p *stats = &s\n\
             _ = p.n\n\
           })\n\
         }",
        // 3. Value-parameter scalar, sub-struct O8 `&x.sub`, and fixed-array mutations
        //    through `&x`, pointer helper, and pointer-receiver method touch only the local copy
        "import \"net/http\"\n\
         struct sub { v int }\n\
         struct mixed {\n\
           m map[string]int\n\
           sub sub\n\
           n int\n\
           xs [2]int\n\
         }\n\
         fn touch_ptr(p *mixed) {\n\
           p.n = 7\n\
           p.xs[0] = 8\n\
         }\n\
         fn (x *mixed) touch_recv() {\n\
           x.n = 9\n\
           x.xs[1] = 10\n\
         }\n\
         fn (x mixed) touch_copy_all(w http.response_writer, r *http.request) {\n\
           slot := &x.sub\n\
           slot.v = 1\n\
           p := &x\n\
           p.n = 2\n\
           p.xs[0] = 3\n\
           touch_ptr(&x)\n\
           x.touch_recv()\n\
         }\n\
         fn main() {\n\
           mx := mixed{m: map[string]int{\"k\": 1}, sub: sub{v: 0}, n: 0, xs: [2]int{0, 0}}\n\
           http.handle_func(\"/x\", mx.touch_copy_all)\n\
           _ = mx\n\
         }",
        // 4. Explicit `managed("...", "interop", ...)` hatch permits the escape
        "import \"net/http\"\n\
         fn main() {\n\
           m := map[string]int{\"k\": 1}\n\
           managed(\"explicit handler lock\", \"interop\", \"#1\") {\n\
             http.handle_func(\"/x\", fn(w http.response_writer, r *http.request) {\n\
               p := &m[\"k\"]\n\
               _ = p\n\
             })\n\
           }\n\
         }",
    ] {
        assert_accepts_clean(src);
    }
}
