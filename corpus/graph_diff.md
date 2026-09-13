# LLBC vs Lean graph diff

- LLBC nodes: 1185, Lean nodes: 1176, merged: 1186 {'type': 119, 'fn': 747, 'const': 58, 'loop_aux': 175, 'trait': 43, 'trait_impl': 44}
- matched by span: 1175; only in LLBC: 10; only in Lean: 1; kind mismatches: 0
- edges: LLBC 1053, Lean 996, in both 991, only LLBC 62, only Lean 5
- non-trivial SCCs: 7

## Ambiguous span keys (cannot be joined)

- lean ('src/join_duplicate.rs', 26, 4, 28, 5, 'loop_aux', 'join_nested_shared_in_loop'): corpus::join_duplicate::join_nested_shared_in_loop::loop#0, corpus::join_duplicate::join_nested_shared_in_loop::loop#1

## Nodes only in LLBC

(Charon-synthesized drop glue already excluded: 36 items)

- `corpus::bst::Tree` (type, src/bst.rs:20) — type alias (Aeneas inlines aliases, no Lean declaration)
- `corpus::hashmap::Hash` (type, src/hashmap.rs:19) — type alias (Aeneas inlines aliases, no Lean declaration)
- `corpus::hashmap::Key` (type, src/hashmap.rs:18) — type alias (Aeneas inlines aliases, no Lean declaration)
- `corpus::issue_194_recursive_struct_projector::AVLTree` (type, src/issue_194_recursive_struct_projector.rs:8) — type alias (Aeneas inlines aliases, no Lean declaration)
- `corpus::loops_nested::HashState` (type, src/loops_nested.rs:94) — type alias (Aeneas inlines aliases, no Lean declaration)
- `corpus::loops_nested_rec::HashState` (type, src/loops_nested_rec.rs:94) — type alias (Aeneas inlines aliases, no Lean declaration)
- `corpus::loops_sequences::HashState` (type, src/loops_sequences.rs:14) — type alias (Aeneas inlines aliases, no Lean declaration)
- `corpus::mini_tree::OptNode` (type, src/mini_tree.rs:7) — type alias (Aeneas inlines aliases, no Lean declaration)
- `corpus::rename_attribute::Test` (type, src/rename_attribute.rs:29) — type alias (Aeneas inlines aliases, no Lean declaration)
- `corpus::tutorial::Bignum` (type, src/tutorial.rs:160) — type alias (Aeneas inlines aliases, no Lean declaration)

## Nodes only in Lean

- `corpus::join_duplicate::join_nested_shared_in_loop::loop#1` (loop_aux, src/join_duplicate.rs:26) lean `join_duplicate.join_nested_shared_in_loop_loop1`

## Kind mismatches (id, llbc kind, lean kind)


## Edges only in LLBC

Categories: default-item: 8, other: 3, type-mention: 51

### default-item

- `corpus::blanket_impl::Trait2` → `corpus::blanket_impl::Trait2::foo` [fn]
- `corpus::constants_lean::Params1` → `corpus::constants_lean::Params1::CT1_LEN` [const]
- `corpus::constants_lean::Params1` → `corpus::constants_lean::Params1::PACKED_LEN` [const]
- `corpus::constants_lean::Trait1` → `corpus::constants_lean::Trait1::NM` [const]
- `corpus::defaulted_method::Trait` → `corpus::defaulted_method::Trait::provided_method` [fn]
- `corpus::rename_attribute::BoolTrait` → `corpus::rename_attribute::BoolTrait::ret_true` [fn]
- `corpus::traits::BoolTrait` → `corpus::traits::BoolTrait::ret_true` [fn]
- `corpus::traits::WithConstTy` → `corpus::traits::WithConstTy::LEN2` [const]

### other

- `corpus::loops::issue500_2::loop#0` → `corpus::loops::issue500_2::bar` [fn]
- `corpus::loops_rec::issue500_2::loop#0` → `corpus::loops_rec::issue500_2::bar` [fn]
- `corpus::static_items::use_static` → `corpus::static_items::use_static::PREFIX` [const]

### type-mention

- `corpus::adt_borrows::use_mut_wrapper` → `corpus::adt_borrows::MutWrapper` [type]
- `corpus::adt_borrows::use_mut_wrapper1` → `corpus::adt_borrows::MutWrapper1` [type]
- `corpus::adt_borrows::use_mut_wrapper2` → `corpus::adt_borrows::MutWrapper2` [type]
- `corpus::adt_borrows::use_shared_wrapper` → `corpus::adt_borrows::SharedWrapper` [type]
- `corpus::adt_borrows::use_shared_wrapper1` → `corpus::adt_borrows::SharedWrapper1` [type]
- `corpus::adt_borrows::use_shared_wrapper2` → `corpus::adt_borrows::SharedWrapper2` [type]
- `corpus::avl::{corpus::avl::Tree<T>}::find` → `corpus::avl::Node` [type]
- `corpus::avl::{corpus::avl::Tree<T>}::find` → `corpus::avl::Ordering` [type]
- `corpus::avl::{corpus::avl::Tree<T>}::insert` → `corpus::avl::Node` [type]
- `corpus::avl::{corpus::avl::Tree<T>}::new` → `corpus::avl::Node` [type]
- `corpus::bst::Tree` → `corpus::bst::Node` [type]
- `corpus::bst::{corpus::bst::TreeSet<T>}::find` → `corpus::bst::Node` [type]
- `corpus::bst::{corpus::bst::TreeSet<T>}::find` → `corpus::bst::Ordering` [type]
- `corpus::bst::{corpus::bst::TreeSet<T>}::insert` → `corpus::bst::Node` [type]
- `corpus::bst::{corpus::bst::TreeSet<T>}::insert` → `corpus::bst::Ordering` [type]
- `corpus::bst::{corpus::bst::TreeSet<T>}::new` → `corpus::bst::Node` [type]
- `corpus::constants::unwrap_y` → `corpus::constants::Wrap` [type]
- `corpus::defaulted_method::main` → `corpus::defaulted_method::NoOverride` [type]
- `corpus::defaulted_method::main` → `corpus::defaulted_method::YesOverride` [type]
- `corpus::glue::mutual::forest_size` → `corpus::glue::mutual::Tree` [type]
- `corpus::glue::mutual::tree_size` → `corpus::glue::mutual::Forest` [type]
- `corpus::hashmap::{corpus::hashmap::HashMap<T>}::clear` → `corpus::hashmap::AList` [type]
- `corpus::hashmap::{corpus::hashmap::HashMap<T>}::new` → `corpus::hashmap::Fraction` [type]
- `corpus::hashmap::{corpus::hashmap::HashMap<T>}::try_resize` → `corpus::hashmap::AList` [type]
- `corpus::hashmap::{corpus::hashmap::HashMap<T>}::try_resize` → `corpus::hashmap::Fraction` [type]
- `corpus::issue_194_recursive_struct_projector::AVLTree` → `corpus::issue_194_recursive_struct_projector::AVLNode` [type]
- `corpus::issue_charon_1172::new` → `corpus::issue_charon_1172::Key` [type]
- `corpus::list_borrows::increment_list` → `corpus::list_borrows::LCell` [type]
- `corpus::loop_shared_loan_in_join::{corpus::loop_shared_loan_in_join::State}::extract::loop#0` → `corpus::loop_shared_loan_in_join::State` [type]
- `corpus::loops::issue500_2` → `corpus::loops::issue500_2::A` [type]
- `corpus::loops::issue500_2::loop#0` → `corpus::loops::issue500_2::A` [type]
- `corpus::loops::issue500_3` → `corpus::loops::issue500_3::A` [type]
- `corpus::loops_rec::issue500_2` → `corpus::loops_rec::issue500_2::A` [type]
- `corpus::loops_rec::issue500_2::loop#0` → `corpus::loops_rec::issue500_2::A` [type]
- `corpus::loops_rec::issue500_3` → `corpus::loops_rec::issue500_3::A` [type]
- `corpus::mini_tree::OptNode` → `corpus::mini_tree::Node` [type]
- `corpus::mini_tree::{corpus::mini_tree::Tree}::explore` → `corpus::mini_tree::Node` [type]
- `corpus::nested_borrows::incr_list` → `corpus::nested_borrows::ListIterMut` [type]
- `corpus::nested_borrows::use_mut_borrow::loop#0` → `corpus::nested_borrows::MutBorrow` [type]
- `corpus::no_nested_borrows::new_pair1` → `corpus::no_nested_borrows::Pair` [type]
- `corpus::no_nested_borrows::test2` → `corpus::no_nested_borrows::EmptyEnum` [type]
- `corpus::no_nested_borrows::test2` → `corpus::no_nested_borrows::Enum` [type]
- `corpus::no_nested_borrows::test2` → `corpus::no_nested_borrows::One` [type]
- `corpus::no_nested_borrows::test2` → `corpus::no_nested_borrows::Pair` [type]
- `corpus::no_nested_borrows::test2` → `corpus::no_nested_borrows::Sum` [type]
- `corpus::no_nested_borrows::test_constants` → `corpus::no_nested_borrows::Pair` [type]
- `corpus::no_nested_borrows::test_constants` → `corpus::no_nested_borrows::StructWithPair` [type]
- `corpus::no_nested_borrows::test_constants` → `corpus::no_nested_borrows::StructWithTuple` [type]
- `corpus::no_nested_borrows::test_list1` → `corpus::no_nested_borrows::List` [type]
- `corpus::no_nested_borrows::test_shared_borrow_enum2` → `corpus::no_nested_borrows::List` [type]
- `corpus::traits::{corpus::traits::TestType<T>}::test` → `corpus::traits::{corpus::traits::TestType<T>}::test::TestType1` [type]


## Edges only in Lean

Categories: other: 1, type-mention: 4

### other

- `corpus::join_duplicate::join_nested_shared_in_loop` → `corpus::join_duplicate::join_nested_shared_in_loop::loop#1` [loop_aux]

### type-mention

- `corpus::loops_issues::loop_consume_u32::loop#0` → `corpus::loops_issues::WrapperU32` [type]
- `corpus::loops_nested::generate_matrix::loop#0` → `corpus::loops_nested::Key` [type]
- `corpus::loops_nested_rec::generate_matrix::loop#0` → `corpus::loops_nested_rec::Key` [type]
- `corpus::nested_borrows::incr_list::loop#0` → `corpus::nested_borrows::List` [type]


## Non-trivial SCCs

- `corpus::avl::{corpus::avl::Node<T>}::insert`, `corpus::avl::{corpus::avl::Node<T>}::insert_in_left`, `corpus::avl::{corpus::avl::Node<T>}::insert_in_right`, `corpus::avl::{corpus::avl::Tree<T>}::insert_in_opt_node`
- `corpus::tutorial::even`, `corpus::tutorial::odd`
- `corpus::glue::mutual::Forest`, `corpus::glue::mutual::Tree`
- `corpus::glue::mutual::forest_size`, `corpus::glue::mutual::tree_size`
- `corpus::glue::mutual::is_even`, `corpus::glue::mutual::is_odd`
- `corpus::list_borrows::LCell`, `corpus::list_borrows::List`
- `corpus::no_nested_borrows::NodeElem`, `corpus::no_nested_borrows::Tree`
