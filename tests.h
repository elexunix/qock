// assumes all included
using namespace formulae;

void test() {  // asserts are executed even without calling
    struct a {};
    struct b {};
    struct c {};
    static_assert(variable_occurs_in_term<a, variable<a>>::value);
    static_assert(variable_occurs_in_atom<a, equal<variable<a>, variable<a>>>::value);
    static_assert(variable_occurs_in_formula<a, forall<a, equal<variable<a>, Zero>>>::value);
    static_assert(variable_occurs_in_term<a, sum<variable<a>, variable<a>>>::value);
    static_assert(variable_occurs_in_formula<a, equal<variable<b>, sum<variable<a>, variable<a>>>>::value);
    static_assert(!variable_occurs_in_formula<a, equal<
        sum<variable<b>, product<variable<c>, variable<b>>>,
        variable<c>
    >>::value);
    static_assert(std::is_same<
        replace_free_variable_with_term<a, sum<variable<b>, variable<c>>, sum<variable<a>, product<variable<b>, variable<a>>>>::result,
        sum<sum<variable<b>, variable<c>>, product<variable<b>, sum<variable<b>, variable<c>>>>
    >::value);
}

template<typename n, typename k>
using is_even = exists<k, equal<n, sum<variable<k>, variable<k>>>>;
template<typename n, typename k>
using is_odd = exists<k, equal<n, S<sum<variable<k>, variable<k>>>>>;

template<typename a>
struct lemma_a_implies_a {
    using b = implication<a, a>;
    using a_implies_b_implies_a = propositional::hypothesis_addition<a, b>;
    using a_implies_b = propositional::hypothesis_addition<a, a>;
    using a_implies_a = apply_modus_ponens<
        apply_modus_ponens<propositional::conditional_modus_ponens<a, b, a>, a_implies_b_implies_a>,  // ~ (a->b) -> (a->a)
        a_implies_b
    >;
    using result = a_implies_a;
    static_assert(std::is_same<result, theorem<implication<a, a>>>::value);
};
template<typename a>
using apply_lemma_a_implies_a = typename lemma_a_implies_a<a>::result;

template<typename a, typename b, typename c, typename th_a_implies_b, typename th_a_implies_c>
struct from_proven__a_implies_b__and__a_implies_c__derive__a_implies_b_and_c {
    static_assert(std::is_same<th_a_implies_b, theorem<implication<a, b>>>::value, "need th_a_implies_b");
    static_assert(std::is_same<th_a_implies_c, theorem<implication<a, c>>>::value, "need th_a_implies_c");
    using b_implies_c_implies_b_and_c = propositional::conjunction_introduction<b, c>;
    using under_a__b_implies_c_implies_b_and_c = apply_modus_ponens<
        propositional::hypothesis_addition<ternary_implication<b, c, conjunction<b, c>>, a>,
        b_implies_c_implies_b_and_c
    >;
    using under_a__b = th_a_implies_b;
    using under_a__c_implies_b_and_c = apply_modus_ponens<
        apply_modus_ponens<
            propositional::conditional_modus_ponens<a, b, implication<c, conjunction<b, c>>>,
            under_a__b_implies_c_implies_b_and_c
        >,
        under_a__b
    >;
    static_assert(std::is_same<under_a__c_implies_b_and_c, theorem<ternary_implication<a, c, conjunction<b, c>>>>::value);
    using under_a__b_and_c = apply_modus_ponens<
        apply_modus_ponens<
            propositional::conditional_modus_ponens<a, c, conjunction<b, c>>,
            under_a__c_implies_b_and_c
        >,
        th_a_implies_c
    >;
    using result = under_a__b_and_c;
    static_assert(std::is_same<under_a__b_and_c, theorem<implication<a, conjunction<b, c>>>>::value);
};

template<typename a, typename b, typename c, typename th_a_implies_b, typename th_b_implies_c>
struct from_proven__a_implies_b__and__b_implies_c__derive__a_implies_c {
    static_assert(std::is_same<th_a_implies_b, theorem<implication<a, b>>>::value, "need th_a_implies_b");
    static_assert(std::is_same<th_b_implies_c, theorem<implication<b, c>>>::value, "need th_b_implies_c");
    using a_implies_b_implies_c = apply_modus_ponens<
        propositional::hypothesis_addition<implication<b, c>, a>,
        th_b_implies_c
    >;
    static_assert(std::is_same<a_implies_b_implies_c, theorem<ternary_implication<a, b, c>>>::value);
    using a_implies_c = apply_modus_ponens<
        apply_modus_ponens<
            propositional::conditional_modus_ponens<a, b, c>,
            a_implies_b_implies_c
        >,
        th_a_implies_b
    >;
    using result = a_implies_c;
    static_assert(std::is_same<result, theorem<implication<a, c>>>::value);
};

template<typename a>
struct lemma_a_and_not_a_implies_false {
    using premise = conjunction<a, negation<a>>;
    using under_premise__a = propositional::left_conjunction_elimination<a, negation<a>>;
    static_assert(std::is_same<under_premise__a, theorem<implication<premise, a>>>::value);
    using under_premise__a_implies_false = propositional::right_conjunction_elimination<a, negation<a>>;
    static_assert(std::is_same<under_premise__a_implies_false, theorem<implication<premise, negation<a>>>>::value);
    using under_premise__false = apply_modus_ponens<
        apply_modus_ponens<
            propositional::conditional_modus_ponens<premise, a, False>,
            under_premise__a_implies_false
        >,
        under_premise__a
    >;
    using result = under_premise__false;
    static_assert(std::is_same<result, theorem<implication<conjunction<a, negation<a>>, False>>>::value);
};

template<typename a, typename b, typename th_a_implies_b, typename th_a_implies_not_b>
struct from_proven__a_implies_b__and__a_implies_not_b__derive__not_a {
    static_assert(std::is_same<th_a_implies_b, theorem<implication<a, b>>>::value, "need th_a_implies_b");
    static_assert(std::is_same<th_a_implies_not_b, theorem<implication<a, negation<b>>>>::value, "need th_a_implies_not_b");
    using a_implies_b_and_not_b = typename from_proven__a_implies_b__and__a_implies_c__derive__a_implies_b_and_c<
        a, b, negation<b>, th_a_implies_b, th_a_implies_not_b
    >::result;
    using b_and_not_b_implies_false = typename lemma_a_and_not_a_implies_false<b>::result;
    static_assert(std::is_same<b_and_not_b_implies_false, theorem<
        implication<conjunction<b, negation<b>>, False>
    >>::value);
    using a_implies_false = typename from_proven__a_implies_b__and__b_implies_c__derive__a_implies_c<
        a, conjunction<b, negation<b>>, False, a_implies_b_and_not_b, b_and_not_b_implies_false
    >::result;
    using result = a_implies_false;
    static_assert(std::is_same<result, theorem<negation<a>>>::value);
};

template<typename h1, typename h2, typename prop, typename th_h1_implies_h2_implies_prop>
struct merging_hypotheses {
    static_assert(std::is_same<th_h1_implies_h2_implies_prop, theorem<ternary_implication<h1, h2, prop>>>::value);
    using h1_and_h2_implies_h1_implies_h2_implies_prop = apply_modus_ponens<
        propositional::hypothesis_addition<ternary_implication<h1, h2, prop>, conjunction<h1, h2>>,
        th_h1_implies_h2_implies_prop
    >;
    using h1_and_h2_implies_h2_implies_prop = apply_modus_ponens<
        apply_modus_ponens<
            propositional::conditional_modus_ponens<conjunction<h1, h2>, h1, implication<h2, prop>>,
            h1_and_h2_implies_h1_implies_h2_implies_prop
        >,
        propositional::left_conjunction_elimination<h1, h2>
    >;
    static_assert(std::is_same<h1_and_h2_implies_h2_implies_prop, theorem<ternary_implication<conjunction<h1, h2>, h2, prop>>>::value);
    using h1_and_h2_implies_prop = apply_modus_ponens<
        apply_modus_ponens<
            propositional::conditional_modus_ponens<conjunction<h1, h2>, h2, prop>,
            h1_and_h2_implies_h2_implies_prop
        >,
        propositional::right_conjunction_elimination<h1, h2>
    >;
    using result = h1_and_h2_implies_prop;
    static_assert(std::is_same<result, implication<conjunction<h1, h2>, prop>>::value);
};

template<typename h1, typename h2, typename prop, typename th_h1_and_h2_implies_prop>
struct splitting_hypotheses {
    static_assert(std::is_same<th_h1_and_h2_implies_prop, theorem<implication<conjunction<h1, h2>, prop>>>::value);
    using h1_and_h2 = conjunction<h1, h2>;
    using h2_implies_h1_and_h2_implies_prop = apply_modus_ponens<
        propositional::hypothesis_addition<implication<h1_and_h2, prop>, h2>,
        th_h1_and_h2_implies_prop
    >;
    using h1_implies_h2_implies_h1_and_h2_implies_prop = apply_modus_ponens<
        propositional::hypothesis_addition<ternary_implication<h2, h1_and_h2, prop>, h1>,
        h2_implies_h1_and_h2_implies_prop
    >;
    static_assert(std::is_same<h1_implies_h2_implies_h1_and_h2_implies_prop, theorem<
        ternary_implication<h1, h2, implication<h1_and_h2, prop>>
    >>::value);
    using h1_implies_h2_implies_h1_and_h2 = propositional::conjunction_introduction<h1, h2>;
    using h1__implies__h2_implies_h1_and_h2_implies_prop__implies__h2_implies_h1_and_h2__implies__h2_implies_prop = apply_modus_ponens<
        propositional::hypothesis_addition<
            ternary_implication<ternary_implication<h2, h1_and_h2, prop>, implication<h2, h1_and_h2>, implication<h2, prop>>,
            h1
        >,
        propositional::conditional_modus_ponens<h2, h1_and_h2, prop>
    >;
    using h1__implies__h2_implies_h1_and_h2__implies__h2_implies_prop = apply_modus_ponens<
        apply_modus_ponens<
            propositional::conditional_modus_ponens<h1, ternary_implication<h2, h1_and_h2, prop>,
                ternary_implication<implication<h2, h1_and_h2>, h2, prop>>,
            h1__implies__h2_implies_h1_and_h2_implies_prop__implies__h2_implies_h1_and_h2__implies__h2_implies_prop
        >,
        h1_implies_h2_implies_h1_and_h2_implies_prop
    >;
    using h1_implies_h2_implies_prop = apply_modus_ponens<
        apply_modus_ponens<
            propositional::conditional_modus_ponens<h1, implication<h2, h1_and_h2>, implication<h2, prop>>,
            h1__implies__h2_implies_h1_and_h2__implies__h2_implies_prop
        >,
        h1_implies_h2_implies_h1_and_h2
    >;
    using result = h1_implies_h2_implies_prop;
    static_assert(std::is_same<result, theorem<ternary_implication<h1, h2, prop>>>::value);
};

template<typename a, typename b, typename th_a_implies_b>
struct contraposition {
    static_assert(std::is_same<th_a_implies_b, theorem<implication<a, b>>>::value);
    using not_b_implies_a_implies_b = apply_modus_ponens<
        propositional::hypothesis_addition<implication<a, b>, negation<b>>,
        th_a_implies_b
    >;
    using not_b_implies_a_implies_not_b = propositional::hypothesis_addition<negation<b>, a>;
    using not_b_and_a_implies_b_and_not_b = typename from_proven__a_implies_b__and__a_implies_not_b__derive__not_a<
        conjunction<negation<b>, a>, b,
        typename merging_hypotheses<negation<b>, a, b, not_b_implies_a_implies_b>::result,
        typename merging_hypotheses<negation<b>, a, negation<b>, not_b_implies_a_implies_not_b>::result
    >::result;
    static_assert(std::is_same<not_b_and_a_implies_b_and_not_b, theorem<
        implication<conjunction<negation<b>, a>, conjunction<b, negation<b>>>
    >>::value);
    using not_b_and_a_implies_false = typename from_proven__a_implies_b__and__b_implies_c__derive__a_implies_c<
        conjunction<negation<b>, a>, conjunction<b, negation<b>>, False,
        not_b_and_a_implies_b_and_not_b,
        typename lemma_a_and_not_a_implies_false<b>::result
    >::result;
    static_assert(std::is_same<not_b_and_a_implies_false, implication<conjunction<negation<b>, a>, False>>::value);
    using not_b_implies_not_a = typename splitting_hypotheses<negation<b>, a, False, not_b_and_a_implies_false>::result;
    using result = not_b_implies_not_a;
    static_assert(std::is_same<result, implication<negation<b>, negation<a>>>::value);
};

template<typename n>
struct proof_that_n_is_either_even_or_odd {
    struct k {};
    using prop_0_is_0_plus_0 = apply_modus_ponens<
        axioms::symmetry_of_equality<sum<Zero, Zero>, Zero>,
        axioms::a_plus_0_is_a<Zero>
    >;
    using prop_forall_k_0_neq_k_plus_k_implies_0_neq_0_plus_0 = firstorder::apply_universal_elimination<k, Zero,
        forall<k, negation<equal<Zero, sum<variable<k>, variable<k>>>>>,
        negation<equal<Zero, sum<Zero, Zero>>>
    >;
    static_assert(std::is_same<prop_forall_k_0_neq_k_plus_k_implies_0_neq_0_plus_0, theorem<
        implication<forall<k, negation<equal<Zero, sum<variable<k>, variable<k>>>>>, negation<equal<Zero, sum<Zero, Zero>>>>
    >>::value);
    using prop_0_neq_0_plus_0_implies_0_eq_0_plus_0 = apply_modus_ponens<
        propositional::hypothesis_addition<equal<Zero, sum<Zero, Zero>>, negation<equal<Zero, sum<Zero, Zero>>>>,
        prop_0_is_0_plus_0
    >;
    using prop_0_neq_0_plus_0_implies_0_neq_0_plus_0 = apply_lemma_a_implies_a<negation<equal<Zero, sum<Zero, Zero>>>>;
    using prop_0_neq_0_plus_0_implies_false = typename from_proven__a_implies_b__and__a_implies_not_b__derive__not_a<
        negation<equal<Zero, sum<Zero, Zero>>>, equal<Zero, sum<Zero, Zero>>,
        prop_0_neq_0_plus_0_implies_0_eq_0_plus_0, prop_0_neq_0_plus_0_implies_0_neq_0_plus_0
    >::result;
    static_assert(std::is_same<prop_0_neq_0_plus_0_implies_false, theorem<
        implication<negation<equal<Zero, sum<Zero, Zero>>>, False>
    >>::value);
    using prop_forall_k_0_neq_k_plus_k_implies_false = typename from_proven__a_implies_b__and__b_implies_c__derive__a_implies_c<
        forall<k, negation<equal<Zero, sum<variable<k>, variable<k>>>>>, negation<equal<Zero, sum<Zero, Zero>>>, False,
        prop_forall_k_0_neq_k_plus_k_implies_0_neq_0_plus_0, prop_0_neq_0_plus_0_implies_false
    >::result;
    using prop_0_is_even = prop_forall_k_0_neq_k_plus_k_implies_false;
    static_assert(std::is_same<prop_0_is_even, theorem<is_even<Zero, k>>>::value);
    using prop_0_is_either_even_or_odd = apply_modus_ponens<
        propositional::left_disjunction_introduction<is_even<Zero, k>, is_odd<Zero, k>>,
        prop_0_is_even
    >;
    static_assert(std::is_same<prop_0_is_either_even_or_odd, theorem<disjunction<is_even<Zero, k>, is_odd<Zero, k>>>>::value);
    // base case: done

    struct m {};
    using premise = disjunction<is_even<variable<m>, k>, is_odd<variable<m>, k>>;
    using goal = disjunction<is_even<S<variable<m>>, k>, is_odd<S<variable<m>>, k>>;
    using subgoal0 = implication<is_even<variable<m>, k>, is_odd<S<variable<m>>, k>>;
    template<typename x, typename phi, typename psi, typename th_exists_x_phi, typename th_phi_implies_psi>
    struct promote_implication_under_existential_quantifier {
        static_assert(std::is_same<th_exists_x_phi, theorem<exists<x, phi>>>::value);
        static_assert(std::is_same<th_phi_implies_psi, theorem<implication<phi, psi>>>::value);
        using prop_not_psi_implies_not_phi = typename contraposition<psi, phi, th_phi_implies_psi>::result;
        using prop_forall_x__not_psi_implies_not_phi = apply_universal_generalization<x,
            prop_not_psi_implies_not_phi,
            forall<x, implication<negation<psi>, negation<phi>>>
        >;
        static_assert(std::is_same<prop_forall_x__not_psi_implies_not_phi, theorem<
            forall<x, implication<negation<psi>, negation<phi>>>
        >>::value);
        struct y {};
        using prop_forall_x_not_psi_implies_not_psi_of_y = firstorder::apply_universal_instantiation<x, variable<y>,
            forall<x, negation<psi>>,
            replace_free_variable_with_term<x, variable<y>, negation<psi>>
        >;
        using prop_not_psi_of_y_implies_not_phi_of_y = apply_modus_ponens<
            firstorder::apply_universal_instantiation<x, variable<y>,
                forall<x, implication<negation<psi>, negation<phi>>>,
                typename replace_free_variable_with_term<x, variable<y>, implication<negation<psi>, negation<phi>>>::result
            >,
            prop_forall_x__not_psi_implies_not_phi
        >;
        using prop_forall_x_not_psi_implies_not_psi_of_y_implies_not_phi_of_y = apply_modus_ponens<
            propositional::hypothesis_addition<
                typename replace_free_variable_with_term<x, variable<y>, implication<negation<psi>, negation<phi>>>::result,
                forall<x, negation<psi>>
            >,
            prop_not_psi_of_y_implies_not_phi_of_y
        >;
        using prop_forall_x_not_psi_implies_not_phi_of_y = apply_modus_ponens<
            apply_modus_ponens<
                propositional::conditional_modus_ponens<
                    forall<x, negation<psi>>,
                    typename replace_free_variable_with_term<x, variable<y>, negation<psi>>::result,
                    typename replace_free_variable_with_term<x, variable<y>, negation<phi>>::result
                >,
                prop_forall_x_not_psi_implies_not_psi_of_y_implies_not_phi_of_y
            >,
            prop_forall_x_not_psi_implies_not_psi_of_y
        >;
        static_assert(std::is_same<prop_forall_x_not_psi_implies_not_phi_of_y, theorem<
            implication<forall<x, negation<psi>>, typename replace_free_variable_with_term<x, variable<y>, negation<phi>>::result>
        >>::value);
        //using prop_forall_x_not_psi_implies_forall_x_not_psi = typename lemma_a_implies_a<forall<x, negation<psi>>>::result;
        using prop_forall_x_not_psi_implies_forall_x_not_phi = apply_universal_generalization<x,
            prop_forall_x_not_psi_implies_not_phi_of_y,
            implication<forall<x, negation<psi>>, forall<x, negation<phi>>>
        >;
        using prop_exists_x_phi_implies_exists_x_psi = typename contraposition<
            forall<x, negation<psi>>, forall<x, negation<phi>>,
            prop_forall_x_not_psi_implies_forall_x_not_phi
        >::result;
        using result = prop_exists_x_phi_implies_exists_x_psi;
        static_assert(std::is_same<prop_exists_x_phi_implies_exists_x_psi, theorem<implication<exists<x, phi>, exists<x, psi>>>>::value);
    };

    using prop_m_equals_k_plus_k_implies_Sm_equals_S_of_k_plus_k = axioms::S_is_a_function<variable<m>, sum<variable<k>, variable<k>>>;
    using prop_forall_k__m_equals_k_plus_k_implies_Sm_equals_S_of_k_plus_k = apply_universal_generalization<k,
        prop_m_equals_k_plus_k_implies_Sm_equals_S_of_k_plus_k,
        forall<k, implication<equal<variable<m>, sum<variable<k>, variable<k>>>, equal<S<variable<m>>, S<sum<variable<k>, variable<k>>>>>>
    >;
    /*using prop_m_is_even_implies_Sm_is_odd = typename promote_implication_under_existential_quantifier<k,
        equal<variable<m>, sum<variable<k>, variable<k>>>,
        equal<S<variable<m>>, S<sum<variable<k>, variable<k>>>>,
        prop_m_equals_k_plus_k_implies_Sm_equals_S_of_k_plus_k
    >::result;
    static_assert(std::is_same<prop_m_is_even_implies_Sm_is_odd, theorem<
        implication<is_even<variable<m>, k>, is_odd<S<variable<m>>, k>>
    >>::value);*/

    // using prop_n_equals_k_plus_k_implies_Sn_equals_S_of_k_plus_k = axioms::S_is_a_function<variable<n>, sum<variable<k>, variable<k>>>;
    // // trick to rename variable
    // struct l {};
    // using prop__forall_l__n_equals_l_plus_l_implies_Sn_equals_S_of_l_plus_l = firstorder::apply_universal_generalization<l, variable<k>,
    //     prop_n_equals_k_plus_k_implies_Sn_equals_S_of_k_plus_k,
    //     forall<l, implication<equal<variable<n>, sum<variable<l>, variable<l>>>, equal<S<variable<n>>, S<sum<variable<l>, variable<l>>>>>>
    // >;
    // struct m {};
    // using prop_n_equals_m_plus_m_implies_Sn_equals_S_of_m_plus_m = firstorder::apply_universal_instantiation<l, variable<m>,
    //     prop__forall_l__n_equals_l_plus_l_implies_Sn_equals_S_of_l_plus_l,
    //     implication<equal<variable<n>, sum<variable<m>, variable<m>>>, equal<S<variable<n>>, S<sum<variable<m>, variable<m>>>>>
    // >;
    // using prop__forall_k__n_equals_k_plus_k_implies_Sn_equals_S_of_k_plus_k = firstorder::apply_universal_generalization<k, variable<m>,
    //     prop_n_equals_m_plus_m_implies_Sn_equals_S_of_m_plus_m,
    //     forall<k, implication<equal<variable<n>, sum<variable<k>, variable<k>>>, equal<S<variable<n>>, S<sum<variable<k>, variable<k>>>>>>
    // >;
    // // yes
};



void test2() {
    /*struct n {};
    using proof = proof_that_n_is_either_even_or_odd<n>;
    using k = proof::k;
    static_assert(is_wellformed_term<variable<n>>::value);
    static_assert(std::is_same<axioms::symmetry_of_equality<variable<n>, variable<n>>, theorem<
        implication<equal<variable<n>, variable<n>>, equal<variable<n>, variable<n>>>
    >>::value);
    static_assert(!std::is_same<axioms::symmetry_of_equality<n, n>,
        implication<equal<n, n>, equal<n, n>> >::value);
    static_assert(std::is_same< axioms::symmetry_of_equality<sum<Zero, Zero>, Zero>, theorem<
        implication<equal<sum<Zero, Zero>, Zero>, equal<Zero, sum<Zero, Zero>>>
    >>::value);
    static_assert(std::is_same<proof::prop_0_is_0_plus_0, theorem<equal<Zero, sum<Zero, Zero>>> >::value);
    static_assert(std::is_same<replace_free_variable_with_term<k, Zero, equal<Zero, sum<variable<k>, variable<k>>>>::result,
        equal<Zero, sum<Zero, Zero>>>::value);*/

    /*static_assert(std::is_same<proof::prop_0_is_even, theorem<
        exists<k, equal<Zero, sum<variable<k>, variable<k>>>>
    >>::value);
    static_assert(std::is_same<proof::prop_0_is_even, theorem<is_even<Zero, k>>>::value);
    static_assert(std::is_same<proof::prop_0_is_either_even_or_odd, theorem<
        disjunction<is_even<Zero, k>, is_odd<Zero, k>>
    >>::value);
    using l = proof::l;
    static_assert(std::is_same<proof::prop__forall_l__n_equals_l_plus_l_implies_Sn_equals_S_of_l_plus_l, theorem<
        forall<l, implication<equal<variable<n>, sum<variable<l>, variable<l>>>, equal<S<variable<n>>, S<sum<variable<l>, variable<l>>>>>>
    >>::value);
    using m = proof::m;
    static_assert(std::is_same<proof::prop_n_equals_m_plus_m_implies_Sn_equals_S_of_m_plus_m, theorem<
        implication<equal<variable<n>, sum<variable<m>, variable<m>>>, equal<S<variable<n>>, S<sum<variable<m>, variable<m>>>>>
    >>::value);
    static_assert(std::is_same<proof::prop__forall_k__n_equals_k_plus_k_implies_Sn_equals_S_of_k_plus_k, theorem<
        forall<k, implication<equal<variable<n>, sum<variable<k>, variable<k>>>, equal<S<variable<n>>, S<sum<variable<k>, variable<k>>>>>>
    >>::value);*/
}

void maintest() {
}