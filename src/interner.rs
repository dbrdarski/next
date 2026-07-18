//! The value interner — hash-consing that makes `==` a pointer comparison (B1).
//!
//! All values are constructed here so that equal values share one allocation.
//! The core operation [`Interner::intern`] probes a structural key (child
//! pointers + leaf content) and returns the existing canonical `ValueRef` on a
//! hit, or installs a fresh one on a miss. Because children are already
//! canonical, this is exact structural deduplication.

use std::collections::HashMap;

use crate::rational::Rational;
use crate::value::{ClosureRef, IndetForm, RecordEntry, ValueData, ValueRef};

/// Owns every interned value for a program. Not `Send`/`Sync` (uses `Rc`); the
/// oracle is sequential (semantics §3).
#[derive(Default)]
pub struct Interner {
    table: HashMap<ValueData, ValueRef>,
}

impl Interner {
    pub fn new() -> Interner {
        Interner::default()
    }

    /// The hash-consing core: return the canonical `ValueRef` for `data`,
    /// creating it if absent. All other constructors funnel through here.
    pub fn intern(&mut self, data: ValueData) -> ValueRef {
        if let Some(existing) = self.table.get(&data) {
            return existing.clone();
        }
        let vref = ValueRef::from_data(data.clone());
        self.table.insert(data, vref.clone());
        vref
    }

    // ── Leaf constructors ────────────────────────────────────────────────────

    pub fn boolean(&mut self, b: bool) -> ValueRef {
        self.intern(ValueData::Boolean(b))
    }

    pub fn null(&mut self) -> ValueRef {
        self.intern(ValueData::Null)
    }

    pub fn number(&mut self, n: Rational) -> ValueRef {
        self.intern(ValueData::Number(n))
    }

    pub fn integer(&mut self, n: i64) -> ValueRef {
        self.number(Rational::from(n))
    }

    /// Intern a string value from Rust text (stored as UTF-16, B1).
    pub fn string(&mut self, s: &str) -> ValueRef {
        self.intern(ValueData::Str(s.encode_utf16().collect()))
    }

    /// Intern a string value from raw UTF-16 code units.
    pub fn string_units(&mut self, units: Vec<u16>) -> ValueRef {
        self.intern(ValueData::Str(units))
    }

    pub fn indeterminate(&mut self, form: IndetForm) -> ValueRef {
        self.intern(ValueData::Indeterminate(form))
    }

    // ── Compound constructors ────────────────────────────────────────────────

    /// Intern a tuple from already-interned elements (order preserved).
    pub fn tuple(&mut self, items: Vec<ValueRef>) -> ValueRef {
        self.intern(ValueData::Tuple(items))
    }

    /// Intern a record from `(key, value)` pairs. Applies **later-wins** on
    /// duplicate keys (RecordCons semantics, E5) and canonicalizes field order by
    /// sorting on the UTF-16 key — record field order is not observable.
    pub fn record(&mut self, fields: Vec<(Vec<u16>, ValueRef)>) -> ValueRef {
        let mut entries: Vec<RecordEntry> = Vec::with_capacity(fields.len());
        for (key, value) in fields {
            match entries.iter_mut().find(|e| e.key == key) {
                Some(e) => e.value = value, // later-wins
                None => entries.push(RecordEntry { key, value }),
            }
        }
        entries.sort_by(|a, b| a.key.cmp(&b.key));
        self.intern(ValueData::Record(entries))
    }

    /// Intern a record from `(&str, value)` pairs — a convenience over
    /// [`Interner::record`].
    pub fn record_str(&mut self, fields: Vec<(&str, ValueRef)>) -> ValueRef {
        let encoded = fields
            .into_iter()
            .map(|(k, v)| (k.encode_utf16().collect(), v))
            .collect();
        self.record(encoded)
    }

    pub fn function(&mut self, closure: ClosureRef) -> ValueRef {
        self.intern(ValueData::Function(closure))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn leaves_intern_to_one_pointer() {
        let mut i = Interner::new();
        assert!(i.boolean(true).ptr_eq(&i.boolean(true)));
        assert!(!i.boolean(true).ptr_eq(&i.boolean(false)));
        assert!(i.null().ptr_eq(&i.null()));
        assert!(i.integer(42).ptr_eq(&i.integer(42)));
        assert!(!i.integer(42).ptr_eq(&i.integer(43)));
        assert!(i.string("hi").ptr_eq(&i.string("hi")));
        assert!(!i.string("hi").ptr_eq(&i.string("ho")));
    }

    #[test]
    fn equal_values_equal_pointers() {
        // `==` is pointer comparison (B1): value equality ⇔ ValueRef equality.
        let mut i = Interner::new();
        assert_eq!(i.integer(7), i.integer(7));
        assert_ne!(i.integer(7), i.string("7"));
    }

    #[test]
    fn number_equality_is_by_value_then_pointer() {
        // 1/2 and 0.5 are the same rational, hence the same interned pointer.
        let mut i = Interner::new();
        let half = i.number(Rational::from_decimal("0.5").unwrap());
        let one_over_two = i.number(Rational::new(1i64.into(), 2i64.into()));
        assert!(half.ptr_eq(&one_over_two));
    }

    #[test]
    fn tuples_hash_cons_structurally() {
        let mut i = Interner::new();
        let (one, two) = (i.integer(1), i.integer(2));
        let a = i.tuple(vec![one.clone(), two.clone()]);
        let b = i.tuple(vec![one.clone(), two.clone()]);
        assert!(a.ptr_eq(&b));
        let c = i.tuple(vec![two, one]);
        assert!(!a.ptr_eq(&c)); // tuple order is observable
    }

    #[test]
    fn nested_tuples_intern() {
        let mut i = Interner::new();
        let one = i.integer(1);
        let two = i.integer(2);
        let inner1 = i.tuple(vec![one.clone()]);
        let inner2 = i.tuple(vec![one]);
        let outer1 = i.tuple(vec![inner1, two.clone()]);
        let outer2 = i.tuple(vec![inner2, two]);
        assert!(outer1.ptr_eq(&outer2));
    }

    #[test]
    fn record_field_order_not_observable() {
        let mut i = Interner::new();
        let one = i.integer(1);
        let two = i.integer(2);
        let ab = i.record_str(vec![("a", one.clone()), ("b", two.clone())]);
        let ba = i.record_str(vec![("b", two), ("a", one)]);
        assert!(ab.ptr_eq(&ba));
    }

    #[test]
    fn record_later_wins_on_duplicate_key() {
        let mut i = Interner::new();
        let (one, two) = (i.integer(1), i.integer(2));
        let dup = i.record_str(vec![("a", one), ("a", two.clone())]);
        let expected = i.record_str(vec![("a", two)]);
        assert!(dup.ptr_eq(&expected));
        assert_eq!(dup.as_record().unwrap().len(), 1);
    }
}
