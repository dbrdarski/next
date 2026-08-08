//! The **AnalysisContract** abstract domain — the analyzer core, §2 of the
//! Application & Induction package (v0.8.1), now in its **structural / correlated**
//! form (the checkpoint-review bridge).
//!
//! **Two-level semantics.** `erase(ac)` is the ordinary contract, whose language
//! denotation `⟦erase(ac)⟧` is untouched. **`γ(ac) ⊆ ⟦erase(ac)⟧`** is the analyzer
//! concretization: the runtime values the complete annotated contract represents,
//! metadata included. Function metadata now survives **structurally** — nested in a
//! tuple, a record field, or a correlated union alternative — so the joint operand
//! state `[callee, …args]` and a correlated union like `[numFn, 5] | [strFn, "hi"]`
//! keep their correlation and never synthesize a false cross-pair (`(numFn, "hi")`).
//!
//! The domain element:
//! - **`Leaf { contract, metadata }`** — a scalar/opaque position. A non-function
//!   member of `⟦contract⟧` is always in γ (metadata is vacuous off function
//!   positions); a function member is in γ iff the metadata admits it — every
//!   function under `Unknown`, or one **realizing** an instance under `Known(S)`.
//! - **`Tuple(elems)` / `Record(fields)`** — positional structure preserved; γ is the
//!   pointwise product, never flattened.
//! - **`Alt(alternatives)`** — a set of **correlated** alternatives; γ is their union,
//!   but each alternative keeps its internal correlation.
//! - **`Bottom`** — `γ = ∅`, the one canonical empty.
//!
//! `prove_subcontract_a` (⊑ᴬ, semantically `γ(a) ⊆ γ(b)`) and `intersect_a` (sound by
//! containment) recurse through the structure; both stay three-valued and
//! deliberately incomplete.

use crate::ast::Lambda;
use crate::contract::{Contract, Kind, Verdict, subcontract};
use crate::env::Binding;
use crate::intern::Interned;
use crate::interner::Interner;
use crate::value::ValueRef;

thread_local! {
    /// Nominal identity for one local branch source. These identifiers never enter a
    /// contract, value, instance, or fact-cache key: branch metadata collapses at
    /// those boundaries (BR-15). Allocation order therefore cannot affect a verdict;
    /// only equality between clones of the same local source is observed.
    static NEXT_BRANCH_SOURCE: std::cell::Cell<u64> = const { std::cell::Cell::new(1) };
}

fn fresh_branch_source() -> u64 {
    NEXT_BRANCH_SOURCE.with(|next| {
        let id = next.get();
        next.set(id.checked_add(1).expect("branch-source identity exhausted"));
        id
    })
}

/// The ordered annotated operands applied to canonical per-function code.
/// Interning the complete tuple makes an instance comparison a pair of pointers,
/// while nested function metadata remains part of each [`AnalysisContract`].
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
struct CaptureContractTuple(Vec<AnalysisContract>);

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
struct InstanceData {
    code: Interned<Lambda>,
    captures: Interned<CaptureContractTuple>,
}

/// A canonical **symbolic analysis instance**: interned per-function code applied
/// to an interned positional tuple of annotated capture contracts. Source spelling
/// and recursive declaration groups are absent from identity.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Instance(Interned<InstanceData>);

impl Instance {
    /// Construct one canonical symbolic application under the active semantic
    /// identity owner. `code` is already α/capture-normalized.
    pub fn new(
        code: Interned<Lambda>,
        captures: Vec<AnalysisContract>,
        interner: &mut Interner,
    ) -> Instance {
        let captures = interner.intern_enum(CaptureContractTuple(captures));
        Instance(interner.intern_enum(InstanceData { code, captures }))
    }

    /// Canonicalize source code and apply the supplied capture contracts in the
    /// canonicalizer's positional free-reference order.
    pub fn from_lambda(
        lambda: &Lambda,
        captures: Vec<AnalysisContract>,
        interner: &mut Interner,
    ) -> Instance {
        let (code, free) = crate::oracle::canonical_function(lambda, interner);
        debug_assert_eq!(free.len(), captures.len());
        Instance::new(code, captures, interner)
    }

    pub fn code(&self) -> &Lambda {
        &self.0.code
    }

    pub fn code_handle(&self) -> Interned<Lambda> {
        self.0.code.clone()
    }

    pub fn captures(&self) -> &[AnalysisContract] {
        &self.0.captures.0
    }

    pub fn act_kind(&self) -> crate::ast::ActKind {
        self.code().act_kind
    }

    pub fn ptr_eq(&self, other: &Instance) -> bool {
        self.0.ptr_eq(&other.0)
    }

    /// Proven-empty when any captured position is bottom — no closure of this shape
    /// can realize it (metadata normalization, §2).
    pub fn is_empty(&self) -> bool {
        self.captures().iter().any(AnalysisContract::is_bottom)
    }
}

/// The instance-metadata lattice element (§2). `Known(∅)` = no function possible
/// (a dead branch — feeds emptiness); `Unknown` = a function is possible, origins
/// coarsened away.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum InstanceMetadata {
    Known(Vec<Instance>),
    Unknown,
}

impl InstanceMetadata {
    /// Join (`∪`): `Known(S) ∪ Known(T) = Known(S ∪ T)`; `X ∪ Unknown = Unknown`.
    pub fn join(a: &InstanceMetadata, b: &InstanceMetadata) -> InstanceMetadata {
        match (a, b) {
            (InstanceMetadata::Known(s), InstanceMetadata::Known(t)) => {
                let mut out = s.clone();
                for i in t {
                    if !out.contains(i) {
                        out.push(i.clone());
                    }
                }
                InstanceMetadata::Known(out)
            }
            _ => InstanceMetadata::Unknown,
        }
    }
}

/// A **held operation image** (DR-16 / DR-17). An operation over finite point operands
/// has an exact result, but computing it is not free and no *result* demand needs it —
/// `⊑ Numeric` is discharged at the producer's mapping. So the ingredients are carried
/// beside the coarse contract and nothing is computed until a **routing** judgment
/// cannot proceed without them.
///
/// Held, not computed: this is the storage that lets the completion walk force **one
/// node** instead of re-running the whole judgment in a different mode.
/// One source assignment in a branch cell. A source is nominal (never a source
/// spelling), so shadowing cannot correlate two unrelated bindings. `choice` is the
/// position in that source's finite point set.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct BranchAssignment {
    source: u64,
    choice: usize,
}

/// One exact branch cell: a compatible source assignment and the point value the
/// represented node has under it.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct BranchCell {
    assignments: Vec<BranchAssignment>,
    value: Contract,
}

/// The exact, analyzer-only relation forced for routing (BR-01/BR-03). It is not a
/// contract and is never interned. Cells retain source assignments so operation
/// composition is a natural join, not an independent Cartesian product.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct BranchSet {
    cells: Vec<BranchCell>,
}

impl BranchSet {
    /// A fresh local source over a finite, non-singleton point contract. Each point is
    /// one cell of that source.
    pub fn source(contract: &Contract) -> Option<BranchSet> {
        let points = crate::contract::point_set(contract)?;
        BranchSet::source_points(points)
    }

    fn source_points(points: Vec<Contract>) -> Option<BranchSet> {
        if points.len() <= 1 {
            return None;
        }
        let source = fresh_branch_source();
        Some(BranchSet {
            cells: points
                .into_iter()
                .enumerate()
                .map(|(choice, value)| BranchCell {
                    assignments: vec![BranchAssignment { source, choice }],
                    value,
                })
                .collect(),
        })
    }

    fn independent(contract: &Contract) -> Option<BranchSet> {
        Some(BranchSet {
            cells: crate::contract::point_set(contract)?
                .into_iter()
                .map(|value| BranchCell {
                    assignments: Vec::new(),
                    value,
                })
                .collect(),
        })
    }

    /// A singleton relation with no source assignments. A non-singleton arm result
    /// without its own relation has lost the mapping from arrivals to outputs, so it
    /// must not be promoted to exact cell metadata by crossing every output with every
    /// arrival.
    pub fn singleton(contract: &Contract) -> Option<BranchSet> {
        let points = crate::contract::point_set(contract)?;
        (points.len() == 1).then(|| BranchSet {
            cells: vec![BranchCell {
                assignments: Vec::new(),
                value: points.into_iter().next().expect("one point"),
            }],
        })
    }

    pub fn cells(&self) -> &[BranchCell] {
        &self.cells
    }

    /// Join the point values of all cells into the ordinary routing contract.
    pub fn contract(&self, interner: &mut Interner) -> Option<Contract> {
        self.cells
            .iter()
            .map(|cell| cell.value.clone())
            .reduce(|a, b| Contract::union(a, b, interner))
    }

    /// Restrict this relation to cells whose point value belongs to `region`.
    pub fn restricted(&self, region: &Contract) -> BranchSet {
        BranchSet {
            cells: self
                .cells
                .iter()
                .filter(|cell| match &cell.value {
                    Contract::Equals(value) => region.contains(value),
                    _ => false,
                })
                .cloned()
                .collect(),
        }
    }

    /// The exact remainder after an unguarded row consumes `region`.
    pub fn without(&self, region: &Contract) -> BranchSet {
        BranchSet {
            cells: self
                .cells
                .iter()
                .filter(|cell| match &cell.value {
                    Contract::Equals(value) => !region.contains(value),
                    _ => false,
                })
                .cloned()
                .collect(),
        }
    }

    pub fn append(&mut self, other: BranchSet) {
        self.cells.extend(other.cells);
    }

    pub fn empty() -> BranchSet {
        BranchSet { cells: Vec::new() }
    }

    /// Narrow a local node by the cells arriving at a routed arm. Only shared
    /// sources constrain it; an independent node keeps its relation unchanged.
    pub fn narrowed_by(&self, arrivals: &BranchSet) -> BranchSet {
        let shares_source = self.cells.iter().any(|cell| {
            cell.assignments.iter().any(|assignment| {
                arrivals.cells.iter().any(|arrival| {
                    arrival
                        .assignments
                        .iter()
                        .any(|candidate| candidate.source == assignment.source)
                })
            })
        });
        if !shares_source {
            return self.clone();
        }
        BranchSet {
            cells: self
                .cells
                .iter()
                .filter(|cell| {
                    arrivals.cells.iter().any(|arrival| {
                        merge_assignments(&cell.assignments, &arrival.assignments).is_some()
                    })
                })
                .cloned()
                .collect(),
        }
    }

    /// Attach a produced relation to the cells that arrived at an arm. Shared
    /// sources must agree; independent sources cross. This is BR-04's structural
    /// correlation and also filters an arm result that still mentions the wider
    /// source relation down to the arrivals that actually selected that arm.
    pub fn join_arrivals(&self, produced: &BranchSet) -> BranchSet {
        let mut cells = Vec::new();
        for arrival in &self.cells {
            for value in &produced.cells {
                if let Some(assignments) =
                    merge_assignments(&arrival.assignments, &value.assignments)
                {
                    cells.push(BranchCell {
                        assignments,
                        value: value.value.clone(),
                    });
                }
            }
        }
        BranchSet { cells }
    }
}

fn merge_assignments(
    left: &[BranchAssignment],
    right: &[BranchAssignment],
) -> Option<Vec<BranchAssignment>> {
    let mut merged = left.to_vec();
    for assignment in right {
        match merged
            .iter()
            .find(|existing| existing.source == assignment.source)
        {
            Some(existing) if existing.choice != assignment.choice => return None,
            Some(_) => {}
            None => merged.push(assignment.clone()),
        }
    }
    merged.sort_by_key(|assignment| assignment.source);
    Some(merged)
}

/// One operand of a held image. Independent finite points cross; a `Branches`
/// operand retains its source assignments; and a nested image lets a chain
/// (`(a * b) * c`) stay lazy and exact through multiple operations.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum ImageOperand {
    Points(Contract),
    Branches(std::rc::Rc<BranchSet>),
    Nested(std::rc::Rc<HeldImage>),
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct HeldImage {
    pub op: crate::ast::PrimOp,
    pub operands: Vec<ImageOperand>,
}

impl ImageOperand {
    fn cardinality_hint(&self) -> usize {
        match self {
            ImageOperand::Points(c) => crate::contract::point_set(c).map_or(0, |s| s.len()),
            ImageOperand::Branches(branches) => branches.cells.len(),
            ImageOperand::Nested(image) => image
                .operands
                .iter()
                .map(ImageOperand::cardinality_hint)
                .fold(1usize, usize::saturating_mul),
        }
    }

    /// Resolve to exact cells, forcing a nested image only when routing asks.
    pub fn force(&self, interner: &mut Interner) -> Option<BranchSet> {
        match self {
            ImageOperand::Points(c) => BranchSet::independent(c),
            ImageOperand::Branches(branches) => Some((**branches).clone()),
            ImageOperand::Nested(image) => image.force_branches(interner),
        }
    }

    /// Make one fresh nominal source when `contract` has multiple finite points.
    pub fn source(contract: &Contract) -> Option<ImageOperand> {
        BranchSet::source(contract)
            .map(|branches| ImageOperand::Branches(std::rc::Rc::new(branches)))
    }

    /// Make a source from the structural annotated domain without erasing it through
    /// an interner. This serves region/fact code that inserts an `AnalysisContract`
    /// directly into a local environment.
    pub fn source_annotated(contract: &AnalysisContract) -> Option<ImageOperand> {
        BranchSet::source_points(contract.finite_points()?)
            .map(|branches| ImageOperand::Branches(std::rc::Rc::new(branches)))
    }
}

impl HeldImage {
    /// Hold an image when every operand is resolvable to finite cells and at least one
    /// operand has multiple cells. There is no fuel or semantic combination budget:
    /// forcing is finite because the represented source cells are finite (BR-16).
    pub fn hold(op: crate::ast::PrimOp, operands: Vec<ImageOperand>) -> Option<HeldImage> {
        let cardinalities: Vec<usize> = operands
            .iter()
            .map(ImageOperand::cardinality_hint)
            .collect();
        if cardinalities.contains(&0) {
            return None;
        }
        if cardinalities.iter().all(|count| *count == 1) {
            return None;
        }
        Some(HeldImage { op, operands })
    }

    /// **Force** the image for routing and erase its cells to their exact joined
    /// contract. Correlation remains available through [`force_branches`](Self::force_branches)
    /// for a downstream held operation.
    pub fn force(&self, interner: &mut Interner) -> Option<Contract> {
        self.force_branches(interner)?.contract(interner)
    }

    /// Force to exact branch cells. Operand relations are combined by natural join:
    /// incompatible assignments of one shared source are discarded, while unrelated
    /// sources form the ordinary Cartesian product. The operation leaf rule is then
    /// applied once to each compatible tuple.
    pub fn force_branches(&self, interner: &mut Interner) -> Option<BranchSet> {
        let relations: Vec<BranchSet> = self
            .operands
            .iter()
            .map(|operand| operand.force(interner))
            .collect::<Option<_>>()?;
        let mut tuples: Vec<(Vec<BranchAssignment>, Vec<Contract>)> =
            vec![(Vec::new(), Vec::new())];
        for relation in relations {
            let mut next = Vec::new();
            for (assignments, values) in &tuples {
                for cell in &relation.cells {
                    let Some(merged) = merge_assignments(assignments, &cell.assignments) else {
                        continue;
                    };
                    let mut tuple = values.clone();
                    tuple.push(cell.value.clone());
                    next.push((merged, tuple));
                }
            }
            tuples = next;
        }
        if tuples.is_empty() {
            return None;
        }
        let mut cells = Vec::with_capacity(tuples.len());
        for (assignments, tuple) in tuples {
            let sets: Vec<Vec<Contract>> = tuple.into_iter().map(|point| vec![point]).collect();
            let value = crate::contract::exact_image_over(self.op, &sets, interner)?;
            cells.push(BranchCell { assignments, value });
        }
        Some(BranchSet { cells })
    }
}

/// The structural / correlated abstract-domain element (§2, bridge form).
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum AnalysisContract {
    /// A scalar/opaque position: an ordinary contract with function-position metadata.
    /// Local held images live in the expression environment, not here, so they cannot
    /// escape through an instance, structure, return, or fact key (BR-15).
    Leaf {
        contract: Contract,
        metadata: InstanceMetadata,
    },
    /// A tuple with positional annotated elements — structure preserved.
    Tuple(Vec<AnalysisContract>),
    /// A record with annotated fields (static string keys).
    Record(Vec<(String, AnalysisContract)>),
    /// A set of **correlated** alternatives — γ is their union; never flattened.
    Alt(Vec<AnalysisContract>),
    /// `γ = ∅` — the one canonical empty.
    Bottom,
}

impl AnalysisContract {
    /// Flatten this annotated element when it is structurally a finite set of point
    /// contracts. Analyzer metadata is retained elsewhere; this only establishes the
    /// local source choices used by branch provenance.
    fn finite_points(&self) -> Option<Vec<Contract>> {
        match self {
            AnalysisContract::Bottom => Some(Vec::new()),
            AnalysisContract::Leaf { contract, .. } => crate::contract::point_set(contract),
            AnalysisContract::Alt(alternatives) => {
                let mut points = Vec::new();
                for alternative in alternatives {
                    points.extend(alternative.finite_points()?);
                }
                Some(points)
            }
            AnalysisContract::Tuple(_) | AnalysisContract::Record(_) => None,
        }
    }

    /// The canonical empty concretization.
    pub fn bottom() -> AnalysisContract {
        AnalysisContract::Bottom
    }

    /// Lift an ordinary contract with coarsened function metadata. Tuple/record
    /// structure and union alternatives remain explicit; opaque leaves carry
    /// `(C, Unknown)`.
    pub fn of_contract(contract: Contract) -> AnalysisContract {
        match contract {
            Contract::Bottom => AnalysisContract::Bottom,
            Contract::Tuple(elements) => AnalysisContract::tuple(
                elements
                    .iter()
                    .map(|element| AnalysisContract::of_contract((**element).clone()))
                    .collect(),
            ),
            Contract::Record(fields) => AnalysisContract::record(
                fields
                    .iter()
                    .map(|(key, value)| {
                        (
                            key.clone(),
                            AnalysisContract::of_contract((**value).clone()),
                        )
                    })
                    .collect(),
            ),
            Contract::Union(left, right) => AnalysisContract::alt(vec![
                AnalysisContract::of_contract((*left).clone()),
                AnalysisContract::of_contract((*right).clone()),
            ]),
            other => AnalysisContract::leaf(other, InstanceMetadata::Unknown),
        }
    }

    /// The most precise fixed representation of a concrete value available from the
    /// live value layer. Aggregate structure is retained, and a NEXT closure carries
    /// its concrete shape plus exact capture contracts. A capture's own function
    /// metadata may remain coarsened because `Equals(capture)` already fixes that value.
    pub fn of_value(value: ValueRef, interner: &mut Interner) -> AnalysisContract {
        if let Some(function) = value.as_fn() {
            let mut environment = Vec::with_capacity(function.free_vars().len());
            for index in 0..function.free_vars().len() {
                let Some(Binding::Value(capture)) = function.capture_binding_at(index) else {
                    return AnalysisContract::of_contract(Contract::Equals(value));
                };
                environment.push(AnalysisContract::of_contract(Contract::Equals(capture)));
            }
            let instance = Instance::new(function.shape_rc(), environment, interner);
            return AnalysisContract::leaf(
                Contract::Equals(value),
                InstanceMetadata::Known(vec![instance]),
            );
        }
        if let Some(items) = value.as_tuple() {
            return AnalysisContract::tuple(
                items
                    .iter()
                    .cloned()
                    .map(|value| AnalysisContract::of_value(value, interner))
                    .collect(),
            );
        }
        if let Some(entries) = value.as_record() {
            let mut fields = Vec::with_capacity(entries.len());
            for entry in entries {
                let Ok(key) = String::from_utf16(&entry.key) else {
                    return AnalysisContract::of_contract(Contract::Equals(value));
                };
                fields.push((
                    key,
                    AnalysisContract::of_value(entry.value.clone(), interner),
                ));
            }
            return AnalysisContract::record(fields);
        }
        AnalysisContract::of_contract(Contract::Equals(value))
    }

    /// A leaf, **normalized** to the one canonical bottom (§2): `(Bottom, _) →
    /// Bottom`, and `(C, Known(∅)) → Bottom` when `C` is function-only (its γ then has
    /// no members at all). Off function positions, `Known(∅)` is vacuous — a
    /// deliberate generalization of the spec's function-position statement (see
    /// `OwedItems`, the `Known(∅)` doc-integration mismatch).
    pub fn leaf(contract: Contract, metadata: InstanceMetadata) -> AnalysisContract {
        if matches!(contract, Contract::Bottom) {
            return AnalysisContract::Bottom;
        }
        if matches!(&metadata, InstanceMetadata::Known(s) if s.is_empty())
            && is_function_only(&contract)
        {
            return AnalysisContract::Bottom;
        }
        AnalysisContract::Leaf { contract, metadata }
    }

    /// A correlated tuple; a bottom element makes the whole tuple bottom.
    pub fn tuple(elems: Vec<AnalysisContract>) -> AnalysisContract {
        if elems.iter().any(AnalysisContract::is_bottom) {
            return AnalysisContract::Bottom;
        }
        AnalysisContract::Tuple(elems)
    }

    /// A record; a bottom field makes the whole record bottom.
    pub fn record(fields: Vec<(String, AnalysisContract)>) -> AnalysisContract {
        if fields.iter().any(|(_, v)| v.is_bottom()) {
            return AnalysisContract::Bottom;
        }
        AnalysisContract::Record(fields)
    }

    /// A union of correlated alternatives, bottom branches dropped; an empty union is
    /// bottom, a singleton collapses.
    pub fn alt(alternatives: Vec<AnalysisContract>) -> AnalysisContract {
        let mut live: Vec<AnalysisContract> = alternatives
            .into_iter()
            .filter(|a| !a.is_bottom())
            .collect();
        match live.len() {
            0 => AnalysisContract::Bottom,
            1 => live.pop().unwrap(),
            _ => AnalysisContract::Alt(live),
        }
    }

    /// `γ(ac) = ∅`.
    pub fn is_bottom(&self) -> bool {
        matches!(self, AnalysisContract::Bottom)
    }

    /// `erase(ac)` — the ordinary contract (the language denotation, metadata dropped).
    pub fn erase(&self, i: &mut Interner) -> Contract {
        match self {
            AnalysisContract::Bottom => Contract::Bottom,
            AnalysisContract::Leaf { contract, .. } => contract.clone(),
            AnalysisContract::Tuple(es) => {
                let elems: Vec<Contract> = es.iter().map(|e| e.erase(i)).collect();
                Contract::tuple(elems, i)
            }
            AnalysisContract::Record(fs) => {
                let fields: Vec<(String, Contract)> =
                    fs.iter().map(|(k, v)| (k.clone(), v.erase(i))).collect();
                Contract::record(fields, i)
            }
            AnalysisContract::Alt(alts) => {
                let parts: Vec<Contract> = alts.iter().map(|a| a.erase(i)).collect();
                parts
                    .into_iter()
                    .reduce(|a, b| Contract::union(a, b, i))
                    .unwrap_or(Contract::Bottom)
            }
        }
    }

    /// Exact structural projection of tuple position `index`. `None` means this domain
    /// cannot prove that every represented producer has that position; callers must
    /// retain the ordinary access rule's conservative result instead.
    pub fn project_index(&self, index: usize, interner: &mut Interner) -> Option<AnalysisContract> {
        match self {
            AnalysisContract::Bottom => Some(AnalysisContract::Bottom),
            AnalysisContract::Tuple(elements) => elements.get(index).cloned(),
            AnalysisContract::Alt(alternatives) => alternatives
                .iter()
                .map(|alternative| alternative.project_index(index, interner))
                .collect::<Option<Vec<_>>>()
                .map(AnalysisContract::alt),
            AnalysisContract::Leaf { contract, .. } => match contract {
                Contract::Tuple(elements) => elements
                    .get(index)
                    .map(|element| AnalysisContract::of_contract((**element).clone())),
                Contract::Equals(value) => value
                    .as_tuple()
                    .and_then(|items| items.get(index).cloned())
                    .map(|value| AnalysisContract::of_value(value, interner)),
                Contract::Union(left, right) => AnalysisContract::alt(vec![
                    AnalysisContract::of_contract((**left).clone()),
                    AnalysisContract::of_contract((**right).clone()),
                ])
                .project_index(index, interner),
                // A member of `A ∩ B` lies in both sides, so **either side's**
                // projection alone is a sound over-approximation of the element —
                // no construction needed (these projectors carry no interner).
                // Prefer an informative side over a `Top` one.
                Contract::Intersection(left, right) => pick_projection(
                    AnalysisContract::of_contract((**left).clone()).project_index(index, interner),
                    AnalysisContract::of_contract((**right).clone()).project_index(index, interner),
                ),
                _ => None,
            },
            AnalysisContract::Record(_) => None,
        }
    }

    /// Exact structural projection of a statically named record field.
    pub fn project_field(&self, name: &str, interner: &mut Interner) -> Option<AnalysisContract> {
        match self {
            AnalysisContract::Bottom => Some(AnalysisContract::Bottom),
            AnalysisContract::Record(fields) => fields
                .iter()
                .find(|(key, _)| key == name)
                .map(|(_, value)| value.clone()),
            AnalysisContract::Alt(alternatives) => alternatives
                .iter()
                .map(|alternative| alternative.project_field(name, interner))
                .collect::<Option<Vec<_>>>()
                .map(AnalysisContract::alt),
            AnalysisContract::Leaf { contract, .. } => match contract {
                Contract::Record(fields) => fields
                    .iter()
                    .find(|(key, _)| key == name)
                    .map(|(_, value)| AnalysisContract::of_contract((**value).clone())),
                Contract::Equals(value) => {
                    let entries = value.as_record()?;
                    let key: Vec<u16> = name.encode_utf16().collect();
                    entries
                        .iter()
                        .find(|entry| entry.key == key)
                        .map(|entry| AnalysisContract::of_value(entry.value.clone(), interner))
                }
                Contract::Union(left, right) => AnalysisContract::alt(vec![
                    AnalysisContract::of_contract((**left).clone()),
                    AnalysisContract::of_contract((**right).clone()),
                ])
                .project_field(name, interner),
                // See `project_index`'s Intersection arm — either side is sound.
                Contract::Intersection(left, right) => pick_projection(
                    AnalysisContract::of_contract((**left).clone()).project_field(name, interner),
                    AnalysisContract::of_contract((**right).clone()).project_field(name, interner),
                ),
                _ => None,
            },
            AnalysisContract::Tuple(_) => None,
        }
    }

    /// Recover the one concrete value represented by this annotated contract, when it
    /// is structurally singleton. This preserves exact-folding behavior even though an
    /// exact aggregate is now carried as annotated tuple/record structure rather than
    /// only as an opaque `Equals(aggregate)` leaf.
    pub fn singleton_value(&self, interner: &mut Interner) -> Option<ValueRef> {
        match self {
            AnalysisContract::Bottom => None,
            AnalysisContract::Leaf { contract, .. } => match contract {
                Contract::Equals(value) => Some(value.clone()),
                _ => None,
            },
            AnalysisContract::Tuple(elements) => {
                let values = elements
                    .iter()
                    .map(|element| element.singleton_value(interner))
                    .collect::<Option<Vec<_>>>()?;
                Some(interner.tuple(values))
            }
            AnalysisContract::Record(fields) => {
                let values = fields
                    .iter()
                    .map(|(key, value)| {
                        value
                            .singleton_value(interner)
                            .map(|value| (key.encode_utf16().collect(), value))
                    })
                    .collect::<Option<Vec<_>>>()?;
                Some(interner.record(values))
            }
            AnalysisContract::Alt(alternatives) => {
                let mut values = alternatives
                    .iter()
                    .map(|alternative| alternative.singleton_value(interner));
                let first = values.next()??;
                values
                    .all(|value| value.is_some_and(|value| value == first))
                    .then_some(first)
            }
        }
    }

    /// Whether the whole annotated contract carries **no** restrictive metadata — every
    /// leaf is `Unknown`. Then `γ(ac) = ⟦erase(ac)⟧`, so an erased-contract inclusion
    /// into it is a sound ⊑ᴬ proof.
    fn metadata_free(&self) -> bool {
        match self {
            AnalysisContract::Bottom => true,
            AnalysisContract::Leaf { metadata, .. } => {
                matches!(metadata, InstanceMetadata::Unknown)
            }
            AnalysisContract::Tuple(es) => es.iter().all(AnalysisContract::metadata_free),
            AnalysisContract::Record(fs) => fs.iter().all(|(_, v)| v.metadata_free()),
            AnalysisContract::Alt(alts) => alts.iter().all(AnalysisContract::metadata_free),
        }
    }
}

impl From<Contract> for AnalysisContract {
    fn from(contract: Contract) -> AnalysisContract {
        AnalysisContract::of_contract(contract)
    }
}

/// Whether `⟦c⟧ ⊆ Functions` — the only case where `Known(∅)` empties the whole
/// concretization (off function positions the metadata is vacuous).
fn is_function_only(c: &Contract) -> bool {
    match c {
        Contract::Kind(Kind::Function) | Contract::Bottom => true,
        Contract::Union(a, b) => is_function_only(a) && is_function_only(b),
        Contract::Intersection(a, b) => is_function_only(a) || is_function_only(b),
        Contract::Equals(v) => v.is_function(),
        _ => false,
    }
}

// ── γ concretization (membership) ────────────────────────────────────────────

/// Whether the closure value `v` **realizes** instance `i`: its μ-canonical shape
/// matches, and each captured value lies in the γ of the matching annotated capture
/// (recursively). A capture bound to a slot / under-init is treated conservatively as
/// unrealized (a sound under-approximation of γ for membership).
pub fn realizes(v: &ValueRef, i: &Instance, interner: &mut Interner) -> bool {
    let Some(f) = v.as_fn() else { return false };
    if f.shape_rc() != i.code_handle() || f.free_vars().len() != i.captures().len() {
        return false;
    }
    // Resolve capture values first, releasing the borrow on `v` before recursing.
    let mut captures: Vec<ValueRef> = Vec::with_capacity(i.captures().len());
    for index in 0..f.free_vars().len() {
        match f.capture_binding_at(index) {
            Some(Binding::Value(cv)) => captures.push(cv),
            _ => return false,
        }
    }
    for (cap, cv) in i.captures().iter().zip(&captures) {
        if !gamma_contains(cap, cv, interner) {
            return false;
        }
    }
    true
}

/// Whether `v ∈ γ(ac)`, recursing through the annotated structure.
pub fn gamma_contains(ac: &AnalysisContract, v: &ValueRef, interner: &mut Interner) -> bool {
    match ac {
        AnalysisContract::Bottom => false,
        AnalysisContract::Leaf {
            contract, metadata, ..
        } => {
            if !contract.contains(v) {
                return false;
            }
            if !v.is_function() {
                return true; // metadata is vacuous off function positions
            }
            match metadata {
                InstanceMetadata::Unknown => true,
                InstanceMetadata::Known(s) => {
                    for i in s {
                        if realizes(v, i, interner) {
                            return true;
                        }
                    }
                    false
                }
            }
        }
        AnalysisContract::Tuple(es) => {
            let Some(items) = v.as_tuple() else {
                return false;
            };
            if items.len() != es.len() {
                return false;
            }
            let items: Vec<ValueRef> = items.to_vec();
            for (e, x) in es.iter().zip(&items) {
                if !gamma_contains(e, x, interner) {
                    return false;
                }
            }
            true
        }
        AnalysisContract::Record(fs) => {
            let Some(entries) = v.as_record() else {
                return false;
            };
            if entries.len() != fs.len() {
                return false;
            }
            let entries: Vec<(Vec<u16>, ValueRef)> = entries
                .iter()
                .map(|e| (e.key.clone(), e.value.clone()))
                .collect();
            for (k, ac) in fs {
                let ku: Vec<u16> = k.encode_utf16().collect();
                let Some((_, xv)) = entries.iter().find(|(ek, _)| *ek == ku) else {
                    return false;
                };
                let xv = xv.clone();
                if !gamma_contains(ac, &xv, interner) {
                    return false;
                }
            }
            true
        }
        AnalysisContract::Alt(alts) => {
            for a in alts {
                if gamma_contains(a, v, interner) {
                    return true;
                }
            }
            false
        }
    }
}

// ── intersectA / meetInstance ────────────────────────────────────────────────

/// The analyzer conjunction — sound by containment only: `γ(A) ∩ γ(B) ⊆
/// γ(intersect_a(A, B))`. Recurses through the structure (tuples pointwise, unions
/// distribute); leaf∩leaf uses the coverage-normalized metadata meet; a mixed
/// structural/leaf pair falls back to a leaf over the erased intersection (sound,
/// coarse). No lower-bound or idempotence reasoning may rest on the result.
/// Choose between two sound projections of the same element (see the
/// `Intersection` arms of `project_index`/`project_field`): both over-approximate,
/// so either may be returned — prefer one that carries information over a bare
/// `Top` leaf.
fn pick_projection(
    a: Option<AnalysisContract>,
    b: Option<AnalysisContract>,
) -> Option<AnalysisContract> {
    let top = |c: &AnalysisContract| {
        matches!(
            c,
            AnalysisContract::Leaf {
                contract: Contract::Top,
                ..
            }
        )
    };
    match (a, b) {
        (Some(a), Some(b)) => Some(if top(&a) && !top(&b) { b } else { a }),
        (Some(a), None) | (None, Some(a)) => Some(a),
        (None, None) => None,
    }
}

pub fn intersect_a(
    a: &AnalysisContract,
    b: &AnalysisContract,
    interner: &mut Interner,
) -> AnalysisContract {
    match (a, b) {
        (AnalysisContract::Bottom, _) | (_, AnalysisContract::Bottom) => AnalysisContract::Bottom,
        (AnalysisContract::Alt(alts), other) | (other, AnalysisContract::Alt(alts)) => {
            let mut out = Vec::new();
            for alt in alts {
                out.push(intersect_a(alt, other, interner));
            }
            AnalysisContract::alt(out)
        }
        (AnalysisContract::Tuple(ea), AnalysisContract::Tuple(eb)) if ea.len() == eb.len() => {
            let mut elems = Vec::with_capacity(ea.len());
            for (x, y) in ea.iter().zip(eb) {
                elems.push(intersect_a(x, y, interner));
            }
            AnalysisContract::tuple(elems)
        }
        (AnalysisContract::Record(fa), AnalysisContract::Record(fb)) if same_keys(fa, fb) => {
            let mut fields = Vec::with_capacity(fa.len());
            for (k, va) in fa {
                let vb = &fb.iter().find(|(k2, _)| k2 == k).unwrap().1;
                fields.push((k.clone(), intersect_a(va, vb, interner)));
            }
            AnalysisContract::record(fields)
        }
        (
            AnalysisContract::Leaf {
                contract: ca,
                metadata: ma,
                ..
            },
            AnalysisContract::Leaf {
                contract: cb,
                metadata: mb,
                ..
            },
        ) => {
            let contract = Contract::intersect(ca.clone(), cb.clone(), interner);
            let metadata = meet_metadata(ma, mb, interner);
            AnalysisContract::leaf(contract, metadata)
        }
        _ => {
            let (ea, eb) = (a.erase(interner), b.erase(interner));
            AnalysisContract::leaf(
                Contract::intersection(ea, eb, interner),
                InstanceMetadata::Unknown,
            )
        }
    }
}

fn same_keys(fa: &[(String, AnalysisContract)], fb: &[(String, AnalysisContract)]) -> bool {
    fa.len() == fb.len() && fa.iter().all(|(k, _)| fb.iter().any(|(k2, _)| k2 == k))
}

/// The metadata meet (leaf level): `Unknown ∩ M = M`; `Known(S) ∩ Known(T)` is the
/// coverage-normalized same-shape meet (`s ⊑ t ⇒ s`, else the [`meet_instance`] of
/// overlapping environments).
fn meet_metadata(
    a: &InstanceMetadata,
    b: &InstanceMetadata,
    interner: &mut Interner,
) -> InstanceMetadata {
    match (a, b) {
        (InstanceMetadata::Unknown, m) | (m, InstanceMetadata::Unknown) => m.clone(),
        (InstanceMetadata::Known(s), InstanceMetadata::Known(t)) => {
            let mut out: Vec<Instance> = Vec::new();
            for si in s {
                for ti in t {
                    if si.code_handle() != ti.code_handle() {
                        continue;
                    }
                    let meet = if matches!(instance_covers(si, ti, interner), Verdict::Proven) {
                        Some(si.clone())
                    } else if matches!(instance_covers(ti, si, interner), Verdict::Proven) {
                        Some(ti.clone())
                    } else {
                        meet_instance(si, ti, interner)
                    };
                    match meet {
                        Some(m) if !m.is_empty() && !out.contains(&m) => out.push(m),
                        _ => {}
                    }
                }
            }
            InstanceMetadata::Known(out)
        }
    }
}

/// The same-shape environment meet. `None` when shapes differ, or when the
/// environment intersection is **proven** empty (a captured position becomes bottom).
pub fn meet_instance(i: &Instance, j: &Instance, interner: &mut Interner) -> Option<Instance> {
    if i.code_handle() != j.code_handle() || i.captures().len() != j.captures().len() {
        return None;
    }
    let mut env = Vec::with_capacity(i.captures().len());
    for (a, b) in i.captures().iter().zip(j.captures()) {
        let m = intersect_a(a, b, interner);
        if m.is_bottom() {
            return None;
        }
        env.push(m);
    }
    Some(Instance::new(i.code_handle(), env, interner))
}

// ── proveSubcontractA — the annotated three-valued subcontract ────────────────

/// The analyzer judgment for `AC₁ ⊑ᴬ AC₂` (semantically `γ(a) ⊆ γ(b)`) — sound,
/// deliberately incomplete, three-valued. Recurses through structure; a `Refuted`
/// witness must be γ-representable; a proof needs erased inclusion **and** either a
/// metadata-free target or leaf-level metadata coverage.
pub fn prove_subcontract_a(
    a: &AnalysisContract,
    b: &AnalysisContract,
    interner: &mut Interner,
) -> Verdict {
    match (a, b) {
        (AnalysisContract::Bottom, _) => Verdict::Proven, // ∅ ⊑ anything
        (AnalysisContract::Alt(alts), _) => {
            // γ(⋃ alts) ⊆ γ(b) ⟺ every alternative ⊑ b.
            for alt in alts {
                let v = prove_subcontract_a(alt, b, interner);
                if !matches!(v, Verdict::Proven) {
                    return v; // an alternative's Refuted/Unproven is the whole verdict
                }
            }
            Verdict::Proven
        }
        (_, AnalysisContract::Alt(alts)) => {
            // a ⊑ some alternative is sound (incomplete for genuine splits).
            for alt in alts {
                if matches!(prove_subcontract_a(a, alt, interner), Verdict::Proven) {
                    return Verdict::Proven;
                }
            }
            prove_by_erasure(a, b, interner)
        }
        (AnalysisContract::Tuple(ea), AnalysisContract::Tuple(eb)) if ea.len() == eb.len() => {
            for (x, y) in ea.iter().zip(eb) {
                if !matches!(prove_subcontract_a(x, y, interner), Verdict::Proven) {
                    return prove_by_erasure(a, b, interner);
                }
            }
            Verdict::Proven
        }
        (AnalysisContract::Record(fa), AnalysisContract::Record(fb)) if same_keys(fa, fb) => {
            for (k, va) in fa {
                let vb = &fb.iter().find(|(k2, _)| k2 == k).unwrap().1;
                if !matches!(prove_subcontract_a(va, vb, interner), Verdict::Proven) {
                    return prove_by_erasure(a, b, interner);
                }
            }
            Verdict::Proven
        }
        _ => prove_by_erasure(a, b, interner),
    }
}

/// The leaf/mixed path: refute through the erased contracts (γ-representable witness
/// only), else prove when erased inclusion holds and the target is metadata-free or
/// both sides are leaves with covering metadata.
fn prove_by_erasure(
    a: &AnalysisContract,
    b: &AnalysisContract,
    interner: &mut Interner,
) -> Verdict {
    let (ea, eb) = (a.erase(interner), b.erase(interner));
    let base = subcontract(&ea, &eb, interner);
    match &base {
        Verdict::Refuted(w) if gamma_contains(a, w, interner) => {
            return Verdict::Refuted(w.clone());
        }
        _ => {}
    }
    if matches!(base, Verdict::Proven) {
        if b.metadata_free() {
            return Verdict::Proven;
        }
        let leaf_covered = match (a, b) {
            (
                AnalysisContract::Leaf { metadata: ma, .. },
                AnalysisContract::Leaf { metadata: mb, .. },
            ) => matches!(covers(ma, mb, interner), Verdict::Proven),
            _ => false,
        };
        if leaf_covered {
            return Verdict::Proven;
        }
    }
    Verdict::Unproven
}

/// Metadata coverage — the `Known(S) ⊑ Known(T)` triage (§2, round 5). Proven-empty
/// sources ignored; every other source (uncertain inhabitance never silently skipped)
/// requires a same-shape target whose annotated environment covers it (⊑ᴬ recursively).
fn covers(s: &InstanceMetadata, t: &InstanceMetadata, interner: &mut Interner) -> Verdict {
    match (s, t) {
        (_, InstanceMetadata::Unknown) => Verdict::Proven,
        (InstanceMetadata::Unknown, InstanceMetadata::Known(_)) => Verdict::Unproven,
        (InstanceMetadata::Known(src), InstanceMetadata::Known(tgt)) => {
            for si in src {
                if si.is_empty() {
                    continue;
                }
                let covered = tgt
                    .iter()
                    .any(|ti| matches!(instance_covers(si, ti, interner), Verdict::Proven));
                if !covered {
                    return Verdict::Unproven;
                }
            }
            Verdict::Proven
        }
    }
}

/// `instance s ⊑ᴬ instance t`: same canonical code, and each positional
/// capture `s[k] ⊑ᴬ t[k]`.
fn instance_covers(s: &Instance, t: &Instance, interner: &mut Interner) -> Verdict {
    if s.code_handle() != t.code_handle() || s.captures().len() != t.captures().len() {
        return Verdict::Unproven;
    }
    for (a, b) in s.captures().iter().zip(t.captures()) {
        if !matches!(prove_subcontract_a(a, b, interner), Verdict::Proven) {
            return Verdict::Unproven;
        }
    }
    Verdict::Proven
}
