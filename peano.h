#ifndef _included_peano
#define _included_peano
#include <type_traits>


namespace terms {
    struct Zero {};
    template<typename>
    struct S {};
    template<typename, typename>
    struct sum {};
    template<typename, typename>
    struct product {};

    template<>
    struct is_wellformed_term<Zero> : std::true_type {};

    template<typename a>
    struct is_wellformed_term<variable<a>> : std::is_empty<a> {};
    template<>
    struct is_wellformed_term<variable<Zero>> : std::false_type {};
    template<typename a>
    struct is_wellformed_term<variable<variable<a>>> : std::false_type {};
    template<typename a>
    struct is_wellformed_term<variable<S<a>>> : std::false_type {};
    template<typename a, typename b>
    struct is_wellformed_term<variable<sum<a, b>>> : std::false_type {};
    template<typename a, typename b>
    struct is_wellformed_term<variable<product<a, b>>> : std::false_type {};

    template<>
    struct is_term_container_composable_with_terminal<S, Zero> : std::true_type {};
    template<>
    struct are_term_containers_composable<S, variable> : std::true_type {};
    template<>
    struct are_term_containers_composable<S, S> : std::true_type {};
    template<>
    struct are_term_containers_composable<S, sum> : std::true_type {};
    template<>
    struct are_term_containers_composable<S, product> : std::true_type {};
    template<>
    struct is_term_container_composable_with_terminal<sum, Zero> : std::true_type {};
    template<>
    struct are_term_containers_composable<sum, variable> : std::true_type {};
    template<>
    struct are_term_containers_composable<sum, S> : std::true_type {};
    template<>
    struct are_term_containers_composable<sum, sum> : std::true_type {};
    template<>
    struct are_term_containers_composable<sum, product> : std::true_type {};
    template<>
    struct is_term_container_composable_with_terminal<product, Zero> : std::true_type {};
    template<>
    struct are_term_containers_composable<product, variable> : std::true_type {};
    template<>
    struct are_term_containers_composable<product, S> : std::true_type {};
    template<>
    struct are_term_containers_composable<product, sum> : std::true_type {};
    template<>
    struct are_term_containers_composable<product, product> : std::true_type {};

    template<typename a>
    struct variable_occurs_in_term<a, Zero> : std::false_type {};
    template<typename a, typename b>
    struct variable_occurs_in_term<a, S<b>> : variable_occurs_in_term<a, b> {};
    template<typename a, typename b, typename c>
    struct variable_occurs_in_term<a, sum<b, c>>
            : switch_type<variable_occurs_in_term<a, b>::value || variable_occurs_in_term<a, c>::value>
            {};
    template<typename a, typename b, typename c>
    struct variable_occurs_in_term<a, product<b, c>>
            : switch_type<variable_occurs_in_term<a, b>::value || variable_occurs_in_term<a, c>::value>
            {};
}


namespace atoms {
    template<typename, typename>
    struct equal {};

    template<>
    struct is_atom_container_composable_with_terminal<equal, Zero> : std::true_type {};
    template<>
    struct are_atom_term_containers_composable<equal, variable> : std::true_type {};
    template<>
    struct are_atom_term_containers_composable<equal, S> : std::true_type {};
    template<>
    struct are_atom_term_containers_composable<equal, sum> : std::true_type {};
    template<>
    struct are_atom_term_containers_composable<equal, product> : std::true_type {};

    template<typename a, typename b, typename c>
    struct variable_occurs_in_atom<a, equal<b, c>>
            : switch_type<variable_occurs_in_term<a, b>::value || variable_occurs_in_term<a, c>::value>
            {};
}


namespace formulae {
    template<typename alpha, typename beta>
    struct replace_free_variable_with_term<alpha, beta, Zero> {
        using result = Zero;
    };
    template<typename alpha, typename beta, typename x>
    struct replace_free_variable_with_term<alpha, beta, S<x>> {
        using result = S<typename replace_free_variable_with_term<alpha, beta, x>::result>;
    };
    template<typename alpha, typename beta, typename x, typename y>
    struct replace_free_variable_with_term<alpha, beta, sum<x, y>> {
        using result = sum<typename replace_free_variable_with_term<alpha, beta, x>::result,
            typename replace_free_variable_with_term<alpha, beta, y>::result>;
    };
    template<typename alpha, typename beta, typename x, typename y>
    struct replace_free_variable_with_term<alpha, beta, product<x, y>> {
        using result = product<typename replace_free_variable_with_term<alpha, beta, x>::result,
            typename replace_free_variable_with_term<alpha, beta, y>::result>;
    };
    template<typename alpha, typename beta, typename x, typename y>
    struct replace_free_variable_with_term<alpha, beta, equal<x, y>> {
        using result = equal<typename replace_free_variable_with_term<alpha, beta, x>::result,
            typename replace_free_variable_with_term<alpha, beta, y>::result>;
    };

    template<typename phi>
    struct some_term_variable_occurs_in_formula<Zero, phi> : std::false_type {};
    template<typename a, typename phi>
    struct some_term_variable_occurs_in_formula<S<a>, phi> : some_term_variable_occurs_in_formula<a, phi> {};
    template<typename a, typename b, typename phi>
    struct some_term_variable_occurs_in_formula<sum<a, b>, phi>
            : switch_type<some_term_variable_occurs_in_formula<a, phi>::value
                || some_term_variable_occurs_in_formula<b, phi>::value>
            {};
    template<typename a, typename b, typename phi>
    struct some_term_variable_occurs_in_formula<product<a, b>, phi>
            : switch_type<some_term_variable_occurs_in_formula<a, phi>::value
                || some_term_variable_occurs_in_formula<b, phi>::value>
            {};

    template<typename phi>
    struct some_term_variable_is_quantified_over_in_formula<Zero, phi> : std::false_type {};
    template<typename a, typename phi>
    struct some_term_variable_is_quantified_over_in_formula<S<a>, phi> : some_term_variable_is_quantified_over_in_formula<a, phi> {};
    template<typename a, typename b, typename phi>
    struct some_term_variable_is_quantified_over_in_formula<sum<a, b>, phi>
            : switch_type<some_term_variable_is_quantified_over_in_formula<a, phi>::value
                || some_term_variable_is_quantified_over_in_formula<b, phi>::value>
            {};
    template<typename a, typename b, typename phi>
    struct some_term_variable_is_quantified_over_in_formula<product<a, b>, phi>
            : switch_type<some_term_variable_is_quantified_over_in_formula<a, phi>::value
                || some_term_variable_is_quantified_over_in_formula<b, phi>::value>
            {};
}

namespace axioms {
    template<typename a>
    using a_equals_a = typename std::conditional<is_wellformed_term<a>::value, theorem<
        equal<a, a>
    >, illformed_axiom>::type;
    template<typename a>
    using equality_is_reflexive = a_equals_a<a>;
    template<typename a>
    using reflexivity_of_equality = equality_is_reflexive<a>;
    template<typename a, typename b>
    using a_equals_b_implies_b_equals_a = typename std::conditional<are_wellformed_terms<a, b>::value, theorem<
        implication<equal<a, b>, equal<b, a>>
    >, illformed_axiom>::type;
    template<typename a, typename b>
    using equality_is_symmetric = a_equals_b_implies_b_equals_a<a, b>;
    template<typename a, typename b>
    using symmetry_of_equality = equality_is_symmetric<a, b>;
    template<typename a, typename b, typename c>
    using a_equals_b_and_b_equals_c_implies_a_equals_c = typename std::conditional<are_wellformed_terms<a, b, c>::value, theorem<
        implication<conjunction<equal<a, b>, equal<b, c>>, equal<a, c>>
    >, illformed_axiom>::type;
    template<typename a, typename b, typename c>
    using equality_is_transitive = a_equals_b_and_b_equals_c_implies_a_equals_c<a, b, c>;
    template<typename a, typename b, typename c>
    using transitivity_of_equality = equality_is_transitive<a, b, c>;

    template<typename a, typename b>
    using S_is_a_function = typename std::conditional<are_wellformed_terms<a, b>::value, theorem<
        implication<equal<a, b>, equal<S<a>, S<b>>>
    >, illformed_axiom>::type;
    template<typename a, typename b, typename c, typename d>
    using sum_is_a_function = typename std::conditional<are_wellformed_terms<a, b, c, d>::value, theorem<
        implication<
            conjunction<equal<a, c>, equal<b, d>>,
            equal<sum<a, b>, sum<c, d>>
        >
    >, illformed_axiom>::type;
    template<typename a, typename b, typename c, typename d>
    using product_is_a_function = typename std::conditional<are_wellformed_terms<a, b, c, d>::value, theorem<
        implication<
            conjunction<equal<a, c>, equal<b, d>>,
            equal<product<a, b>, product<c, d>>
        >
    >, illformed_axiom>::type;

    template<typename a>
    using S_neq_0 = typename std::conditional<is_wellformed_term<a>::value, theorem<
        negation<equal<S<a>, Zero>>
    >, illformed_axiom>::type;
    template<typename a, typename b>
    using S_is_injective = typename std::conditional<are_wellformed_terms<a, b>::value, theorem<
        implication<equal<S<a>, S<b>>, equal<a, b>>
    >, illformed_axiom>::type;
    template<typename a>
    using a_plus_0_is_a = typename std::conditional<is_wellformed_term<a>::value, theorem<
        equal<sum<a, Zero>, a>
    >, illformed_axiom>::type;
    template<typename a, typename b>
    using a_plus_Sb_is_S_of_a_plus_b = typename std::conditional<are_wellformed_terms<a, b>::value, theorem<
        equal<sum<a, S<b>>, S<sum<a, b>>>
    >, illformed_axiom>::type;
    template<typename a>
    using a_times_0_is_0 = typename std::conditional<is_wellformed_term<a>::value, theorem<
        equal<product<a, Zero>, Zero>
    >, illformed_axiom>::type;
    template<typename a, typename b>
    using a_times_Sb_is_a_times_b_plus_a = typename std::conditional<are_wellformed_terms<a, b>::value, theorem<
        equal<product<a, S<b>>, sum<product<a, b>, a>>
    >, illformed_axiom>::type;

    template<typename n, typename phi>
    using induction = typename std::conditional<is_wff<forall<n, phi>>::value, theorem<
        ternary_implication<
            typename replace_free_variable_with_term<n, Zero, phi>::result,
            implication<phi, replace_free_variable_with_term<n, S<n>, phi>>,
            phi
        >
    >, illformed_axiom>::type;
}


#endif