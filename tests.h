#include "propositional_lib.h"

using namespace formulae;

void test() {
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

template<typename x, typename phi, typename psi>
struct conditionally_perform_implication_under_existential_quantifier_h {
                // proves the following implication: (exists x phi) and (forall x (phi -> psi)) -> (exists x psi)
    // that is, we are given:
    // forall x not phi -> false
    // forall x (phi -> psi)
    // and we want to prove that:
    // forall x not psi -> false
    using premise = conjunction<conjunction<negation<forall<x, negation<phi>>>, forall<x, implication<phi, psi>>>, forall<x, negation<psi>>>;
    // we are about to derive False from it!
    using prop_premise_implies_not_psi = apply_conditional_modus_ponens<
        add_hypothesis<premise, firstorder::apply_universal_instantiation<x, variable<x>, forall<x, negation<psi>>, negation<psi>>>,
        use_library_lemma<implication<premise, forall<x, negation<psi>>>>
    >;
    using prop_premise_implies_phi_implies_psi = apply_conditional_modus_ponens<
        add_hypothesis<premise,
            firstorder::apply_universal_instantiation<x, variable<x>, forall<x, implication<phi, psi>>, implication<phi, psi>>
        >,
        use_library_lemma<implication<premise, forall<x, implication<phi, psi>>>>
    >;
    using prop_premise_implies_not_psi_implies_not_phi = apply_modus_ponens<
        use_library_lemma<implication<
            ternary_implication<premise, phi, psi>,
            ternary_implication<premise, negation<psi>, negation<phi>>
        >>,
        prop_premise_implies_phi_implies_psi
    >;
    using prop_premise_implies_not_phi = apply_conditional_modus_ponens<
        prop_premise_implies_not_psi_implies_not_phi,
        prop_premise_implies_not_psi
    >;
    using prop_premise_implies_forall_x_not_phi = apply_universal_generalization<x,
        prop_premise_implies_not_phi,
        implication<premise, forall<x, negation<phi>>>
    >;
    using prop_premise_implies_forall_x_not_phi_implies_false = use_library_lemma<implication<premise, negation<forall<x, negation<phi>>>>>;
    using prop_premise_implies_false_that_way = apply_conditional_modus_ponens<
        prop_premise_implies_forall_x_not_phi_implies_false,
        prop_premise_implies_forall_x_not_phi
    >;
    using final_premise = conjunction<exists<x, phi>, forall<x, implication<phi, psi>>>;
    using prop_final_premise_implies_forall_x_psi_implies_false = split_hypotheses<prop_premise_implies_false_that_way>;
    using result = prop_final_premise_implies_forall_x_psi_implies_false;
    static_assert(std::is_same_v<result, theorem<implication<conjunction<exists<x, phi>, forall<x, implication<phi, psi>>>, exists<x, psi>>>>);
};
template<typename x, typename phi, typename psi>
using conditionally_perform_implication_under_existential_quantifier
    = typename conditionally_perform_implication_under_existential_quantifier_h<x, phi, psi>::result;
/*template<typename th_exists_x_phi, typename th__forall_x__phi_implies_psi>
struct actually_perform_implication_under_existential_quantifier_h {};
template<typename x, typename phi, typename psi>
struct actually_perform_implication_under_existential_quantifier_h<theorem<exists<x, phi>>, theorem<forall<x, implication<phi, psi>>>> {
    using th_exists_x_phi = theorem<exists<x, phi>>;
    using th__forall_x__phi_implies_psi = theorem<forall<x, implication<phi, psi>>>;
    using prop___exists_x_phi___and___forall_x__phi_implies_psi = apply_modus_ponens_twice<
        propositional::conjunction_introduction<exists<x, phi>, forall<x, implication<phi, psi>>>,
        th_exists_x_phi,
        th__forall_x__phi_implies_psi
    >;
    using th_exists_x_psi = apply_modus_ponens<
        conditionally_perform_implication_under_existential_quantifier<x, phi, psi>,
        prop___exists_x_phi___and___forall_x__phi_implies_psi
    >;
    using result = th_exists_x_phi;
    static_assert(std::is_same_v<result, theorem<exists<x, phi>>>);
};
template<typename th_exists_x_phi, typename th__forall_x__phi_implies_psi>
using actually_perform_implication_under_existential_quantifier
    = typename actually_perform_implication_under_existential_quantifier_h<th_exists_x_phi, th__forall_x__phi_implies_psi>::result;*/

template<typename alpha, typename th_premise, typename conclusion>
struct unconditionally_apply_universal_generalization_h {
    using th_true_implies_premise = add_hypothesis<True, th_premise>;
    using th_true_implies_conclusion = apply_universal_generalization<alpha, th_true_implies_premise, implication<True, conclusion>>;
    using th_conclusion = apply_modus_ponens<
        use_library_lemma<implication<implication<True, conclusion>, conclusion>>,
        th_true_implies_conclusion
    >;
    using result = th_conclusion;
    static_assert(std::is_same_v<result, theorem<conclusion>>);
};
template<typename alpha, typename th_premise, typename conclusion>
using unconditionally_apply_universal_generalization
    = typename unconditionally_apply_universal_generalization_h<alpha, th_premise, conclusion>::result;

template<typename alpha, typename phi>
struct try_to_implicationally_remove_vacuous_existential_quantifier_h {
    static_assert(!variable_occurs_in_formula<alpha, phi>::value);
    using premise = conjunction<negation<forall<alpha, negation<phi>>>, negation<phi>>;
    using prop_premise_implies_forall_alpha_not_phi = apply_universal_generalization<alpha,
        propositional::right_conjunction_elimination<exists<alpha, phi>, negation<phi>>,
        implication<premise, forall<alpha, negation<phi>>>
    >;
    using prop_premise_implies_not_forall_alpha_not_phi = propositional::left_conjunction_elimination<exists<alpha, phi>, negation<phi>>;
    using prop_premise_implies_false = apply_conditional_modus_ponens<
        add_hypothesis<premise,
            use_library_lemma<implication<conjunction<forall<alpha, negation<phi>>, negation<forall<alpha, negation<phi>>>>, False>>
        >,
        apply_modus_ponens<
            use_library_lemma<implication<
                conjunction<implication<premise, forall<alpha, negation<phi>>>, implication<premise, negation<forall<alpha, negation<phi>>>>>,
                implication<premise, conjunction<forall<alpha, negation<phi>>, negation<forall<alpha, negation<phi>>>>>
            >>,
            apply_modus_ponens_twice<
                propositional::conjunction_introduction<
                    implication<premise, forall<alpha, negation<phi>>>,
                    implication<premise, negation<forall<alpha, negation<phi>>>>
                >,
                prop_premise_implies_forall_alpha_not_phi,
                prop_premise_implies_not_forall_alpha_not_phi
            >
        >
    >;
    using final_premise = exists<alpha, phi>;
    static_assert(std::is_same_v<prop_premise_implies_false, theorem<implication<conjunction<final_premise, negation<phi>>, False>>>);
    using prop_final_premise_implies_not_not_phi = split_hypotheses<prop_premise_implies_false>;
    using prop_final_premise_implies_phi = apply_conditional_modus_ponens<
        add_hypothesis<final_premise, use_library_lemma<implication<negation<negation<phi>>, phi>>>,
        prop_final_premise_implies_not_not_phi
    >;
    using result = prop_final_premise_implies_phi;
    static_assert(std::is_same_v<result, theorem<implication<exists<alpha, phi>, phi>>>);
};
template<typename alpha, typename phi>
using try_to_implicationally_remove_vacuous_existential_quantifier
    = typename try_to_implicationally_remove_vacuous_existential_quantifier_h<alpha, phi>::result;

template<typename a, typename b, template<typename> typename phi>
struct try_to_implicationally_silently_replace_variable_A_h {
    static_assert(!std::is_same_v<a, b>);
    static_assert(!variable_occurs_in_formula<a, typename phi<b>::type>::value);
    using phi_of_a = typename phi<a>::type;
    static_assert(!variable_occurs_in_formula<b, typename phi<a>::type>::value);
    // our goal: forall a phi(a) -> forall b phi(b)
    using prop_forall_a_phi_of_a_implies_phi_of_b = firstorder::apply_universal_instantiation<a, variable<b>,
        forall<a, typename phi<a>::type>,
        typename phi<b>::type
    >;
    using prop_forall_a_phi_of_a_implies_forall_b_phi_of_b = apply_universal_generalization<b,
        prop_forall_a_phi_of_a_implies_phi_of_b,
        implication<forall<a, typename phi<a>::type>, forall<b, typename phi<b>::type>>
    >;
    using result = prop_forall_a_phi_of_a_implies_forall_b_phi_of_b;
    static_assert(std::is_same_v<result, theorem<implication<forall<a, typename phi<a>::type>, forall<b, typename phi<b>::type>>>>);
};
template<typename a, typename b, template<typename> typename phi>
using try_to_implicationally_silently_replace_variable_A = typename try_to_implicationally_silently_replace_variable_A_h<a, b, phi>::result;
template<typename a, typename b, template<typename> typename phi>
struct try_to_implicationally_silently_replace_variable_E_h {
    static_assert(!std::is_same_v<a, b>);
    static_assert(!variable_occurs_in_formula<a, typename phi<b>::type>::value);
    static_assert(!variable_occurs_in_formula<b, typename phi<a>::type>::value);
    // our goal: exists a phi(a) -> exists b phi(b)
    // that is, forall b not phi(b) -> forall a not phi(a)
    template<typename var>
    struct helper_template {
        using type = negation<typename phi<var>::type>;
    };
    using prop_forall_b_not_phi_of_b_implies_forall_a_not_phi_of_a = try_to_implicationally_silently_replace_variable_A<b, a, helper_template>;
    using prop_not_forall_a_not_phi_of_a_implies_not_forall_b_not_phi_of_b = apply_modus_ponens<
        use_library_lemma<implication<
            implication<forall<b, negation<typename phi<b>::type>>, forall<a, negation<typename phi<a>::type>>>,
            implication<negation<forall<a, negation<typename phi<a>::type>>>, negation<forall<b, negation<typename phi<b>::type>>>>
        >>,
        prop_forall_b_not_phi_of_b_implies_forall_a_not_phi_of_a
    >;
    using result = prop_not_forall_a_not_phi_of_a_implies_not_forall_b_not_phi_of_b;
    static_assert(std::is_same_v<result, theorem<
        implication<exists<a, typename phi<a>::type>, exists<b, typename phi<b>::type>>
    >>);
};
template<typename a, typename b, template<typename> typename phi>
using try_to_implicationally_silently_replace_variable_E = typename try_to_implicationally_silently_replace_variable_E_h<a, b, phi>::result;

template<typename n>
struct proof_that_n_is_either_even_or_odd {
    struct k {};
    template<typename term>
    using statement_for = disjunction<is_even<term, k>, is_odd<term, k>>;

    using prop_0_is_0_plus_0 = apply_modus_ponens<
        axioms::symmetry_of_equality<sum<Zero, Zero>, Zero>,
        axioms::a_plus_0_is_a<Zero>
    >;
    using prop_forall_k_0_neq_k_plus_k_implies_0_neq_0_plus_0 = firstorder::apply_universal_elimination<k, Zero,
        forall<k, negation<equal<Zero, sum<variable<k>, variable<k>>>>>,
        negation<equal<Zero, sum<Zero, Zero>>>
    >;
    static_assert(std::is_same_v<prop_forall_k_0_neq_k_plus_k_implies_0_neq_0_plus_0, theorem<
        implication<forall<k, negation<equal<Zero, sum<variable<k>, variable<k>>>>>, negation<equal<Zero, sum<Zero, Zero>>>>
    >>);
    using prop_0_neq_0_plus_0_implies_false = apply_modus_ponens<
        use_library_lemma<implication<equal<Zero, sum<Zero, Zero>>, negation<negation<equal<Zero, sum<Zero, Zero>>>>>>,
        prop_0_is_0_plus_0
    >;
    static_assert(std::is_same_v<prop_0_neq_0_plus_0_implies_false, theorem<implication<negation<equal<Zero, sum<Zero, Zero>>>, False>>>);
    using prop_forall_k_0_neq_k_plus_k_implies_false = apply_modus_ponens_twice<
        use_library_lemma<ternary_implication<
            implication<forall<k, negation<equal<Zero, sum<variable<k>, variable<k>>>>>, negation<equal<Zero, sum<Zero, Zero>>>>,
            implication<negation<equal<Zero, sum<Zero, Zero>>>, False>,
            implication<forall<k, negation<equal<Zero, sum<variable<k>, variable<k>>>>>, False>
        >>,
        prop_forall_k_0_neq_k_plus_k_implies_0_neq_0_plus_0,
        prop_0_neq_0_plus_0_implies_false
    >;
    using prop_0_is_even = prop_forall_k_0_neq_k_plus_k_implies_false;
    static_assert(std::is_same_v<prop_0_is_even, theorem<is_even<Zero, k>>>);
    using prop_0_is_either_even_or_odd = apply_modus_ponens<
        propositional::left_disjunction_introduction<is_even<Zero, k>, is_odd<Zero, k>>,
        prop_0_is_even
    >;
    static_assert(std::is_same_v<prop_0_is_either_even_or_odd, theorem<statement_for<Zero>>>);
    // base case: done

    //struct m {};
    using m = n;
    using premise = disjunction<is_even<variable<m>, k>, is_odd<variable<m>, k>>;
    using goal = disjunction<is_even<S<variable<m>>, k>, is_odd<S<variable<m>>, k>>;

    using subgoal0 = implication<is_even<variable<m>, k>, is_odd<S<variable<m>>, k>>;
    using prop_m_equals_k_plus_k_implies_Sm_equals_S_of_k_plus_k = axioms::S_is_a_function<variable<m>, sum<variable<k>, variable<k>>>;
    using prop__forall_k__m_equals_k_plus_k_implies_Sm_equals_S_of_k_plus_k = unconditionally_apply_universal_generalization<k,
        prop_m_equals_k_plus_k_implies_Sm_equals_S_of_k_plus_k,
        forall<k, implication<equal<variable<m>, sum<variable<k>, variable<k>>>, equal<S<variable<m>>, S<sum<variable<k>, variable<k>>>>>>
    >;
    using prop_m_is_even_implies_Sm_is_odd = apply_modus_ponens<
        swap_hypotheses_in_implication<split_hypotheses<
            conditionally_perform_implication_under_existential_quantifier<k,
                equal<variable<m>, sum<variable<k>, variable<k>>>,
                equal<S<variable<m>>, S<sum<variable<k>, variable<k>>>>
            >
        >>,
        prop__forall_k__m_equals_k_plus_k_implies_Sm_equals_S_of_k_plus_k
    >;
    static_assert(std::is_same_v<prop_m_is_even_implies_Sm_is_odd, theorem<subgoal0>>);

    using subgoal1 = implication<is_odd<variable<m>, k>, is_even<S<variable<m>>, k>>;
    template<typename a, typename b, typename c>
    struct lemma_a_equals_b_implies_b_equals_c_implies_a_equals_c {
        using result = apply_conditional_conditional_modus_ponens<
            add_hypothesis<equal<a, b>, add_hypothesis<equal<b, c>, axioms::transitivity_of_equality<a, b, c>>>,
            apply_conditional_conditional_modus_ponens_twice<
                add_hypothesis<equal<a, b>, add_hypothesis<equal<b, c>, propositional::conjunction_introduction<equal<a, b>, equal<b, c>>>>,
                propositional::hypothesis_addition<equal<a, b>, equal<b, c>>,
                add_hypothesis<equal<a, b>, use_library_lemma<implication<equal<b, c>, equal<b, c>>>>
            >
        >;
        static_assert(std::is_same_v<result, theorem<ternary_implication<equal<a, b>, equal<b, c>, equal<a, c>>>>);
    };
    template<typename a, typename b, typename c, typename d>
    struct lemma_a_equals_b_implies_b_equals_c_implies_c_equals_d_implies_a_equals_d {
        using prop_a_equals_b_implies_b_equals_c_implies_c_equals_d_implies_b_equals_d = add_hypothesis<equal<a, b>,
            typename lemma_a_equals_b_implies_b_equals_c_implies_a_equals_c<b, c, d>::result
        >;
        using prop_a_equals_b_implies_b_equals_c_implies_c_equals_d_implies_a_equals_b = use_library_lemma<
            multiary_implication<equal<a, b>, equal<b, c>, equal<c, d>, equal<a, b>>
        >;
        using prop_a_equals_b_implies_b_equals_c_implies_c_equals_d_implies_a_equals_d = apply_cccmp_twice<
            add_hypothesis<equal<a, b>, add_hypothesis<equal<b, c>, add_hypothesis<equal<c, d>,
                typename lemma_a_equals_b_implies_b_equals_c_implies_a_equals_c<a, b, d>::result
            >>>,
            prop_a_equals_b_implies_b_equals_c_implies_c_equals_d_implies_a_equals_b,
            prop_a_equals_b_implies_b_equals_c_implies_c_equals_d_implies_b_equals_d
        >;
        using result = prop_a_equals_b_implies_b_equals_c_implies_c_equals_d_implies_a_equals_d;
        static_assert(std::is_same_v<result, theorem<
            multiary_implication<equal<a, b>, equal<b, c>, equal<c, d>, equal<a, d>>
        >>);
    };
    template<typename a, typename b>
    struct lemma_Sa_plus_b_equals_S_of_a_plus_b__implementation_for_different_variables {  // by induction on b
        static_assert(!std::is_same_v<a, b>);
        template<typename a_prime, typename b_prime>
        using statement = equal<sum<S<a_prime>, b_prime>, S<sum<a_prime, b_prime>>>;
        using prop_Sa_plus_0_equals_Sa = axioms::a_plus_0_is_a<S<variable<a>>>;
        using prop_Sa_equals_S_of_a_plus_0 = apply_modus_ponens<
            axioms::S_is_a_function<variable<a>, sum<variable<a>, Zero>>,
            apply_modus_ponens<axioms::equality_is_symmetric<sum<variable<a>, Zero>, variable<a>>, axioms::a_plus_0_is_a<variable<a>>>
        >;
        using prop_Sa_plus_0_equals_S_of_a_plus_0 = apply_modus_ponens<
            axioms::equality_is_transitive<sum<S<variable<a>>, Zero>, S<variable<a>>, S<sum<variable<a>, Zero>>>,
            apply_modus_ponens_twice<
                propositional::conjunction_introduction<
                    equal<sum<S<variable<a>>, Zero>, S<variable<a>>>,
                    equal<S<variable<a>>, S<sum<variable<a>, Zero>>>
                >,
                prop_Sa_plus_0_equals_Sa,
                prop_Sa_equals_S_of_a_plus_0
            >
        >;
        static_assert(std::is_same_v<prop_Sa_plus_0_equals_S_of_a_plus_0, theorem<statement<variable<a>, Zero>>>);
        using premise = statement<variable<a>, variable<b>>;
        using prop_Sa_plus_Sb_equals_S_of_Sa_plus_b = axioms::a_plus_Sb_is_S_of_a_plus_b<S<variable<a>>, variable<b>>;
        using prop_premise_implies_S_of_Sa_plus_b_equals_SS_of_a_plus_b
            = axioms::S_is_a_function<sum<S<variable<a>>, variable<b>>, S<sum<variable<a>, variable<b>>>>;
        using prop_SS_of_a_plus_b_equals_S_of_a_plus_Sb = apply_modus_ponens<
            axioms::S_is_a_function<S<sum<variable<a>, variable<b>>>, sum<variable<a>, S<variable<b>>>>,
            apply_modus_ponens<
                axioms::symmetry_of_equality<sum<variable<a>, S<variable<b>>>, S<sum<variable<a>, variable<b>>>>,
                axioms::a_plus_Sb_is_S_of_a_plus_b<variable<a>, variable<b>>
            >
        >;
        using prop_premise_implies_Sa_plus_Sb_equals_S_of_a_plus_Sb = apply_conditional_modus_ponens_thrice<
            add_hypothesis<premise, typename lemma_a_equals_b_implies_b_equals_c_implies_c_equals_d_implies_a_equals_d<
                sum<S<variable<a>>, S<variable<b>>>,
                S<sum<S<variable<a>>, variable<b>>>,
                S<S<sum<variable<a>, variable<b>>>>,
                S<sum<variable<a>, S<variable<b>>>>
            >::result>,
            add_hypothesis<premise, prop_Sa_plus_Sb_equals_S_of_Sa_plus_b>,
            prop_premise_implies_S_of_Sa_plus_b_equals_SS_of_a_plus_b,
            add_hypothesis<premise, prop_SS_of_a_plus_b_equals_S_of_a_plus_Sb>
        >;
        static_assert(std::is_same_v<prop_premise_implies_Sa_plus_Sb_equals_S_of_a_plus_Sb, theorem<
            implication<statement<variable<a>, variable<b>>, statement<variable<a>, S<variable<b>>>>
        >>);
        using result = apply_modus_ponens_twice<
            axioms::induction<b, statement<variable<a>, variable<b>>>,
            prop_Sa_plus_0_equals_S_of_a_plus_0,
            prop_premise_implies_Sa_plus_Sb_equals_S_of_a_plus_Sb
        >;
        static_assert(std::is_same_v<result, theorem<statement<variable<a>, variable<b>>>>);
    };
    template<typename a>
    struct lemma_Sa_plus_b_equals_S_of_a_plus_b__implementation_for_identical_variables {
        struct b {};
        using result_for_ab = typename lemma_Sa_plus_b_equals_S_of_a_plus_b__implementation_for_different_variables<a, b>::result;
        template<typename a_prime, typename b_prime>
        using statement = typename lemma_Sa_plus_b_equals_S_of_a_plus_b__implementation_for_different_variables<a, b>
            ::template statement<a_prime, b_prime>;
        static_assert(std::is_same_v<result_for_ab, theorem<
            statement<variable<a>, variable<b>>
        >>);
        using gen = unconditionally_apply_universal_generalization<b, result_for_ab, forall<b, statement<variable<a>, variable<b>>>>;
        using inst = apply_modus_ponens<
            firstorder::apply_universal_instantiation<b, variable<a>, forall<b, statement<variable<a>, variable<b>>>, statement<variable<a>, variable<a>>>,
            gen
        >;
        using result = inst;
        static_assert(std::is_same_v<result, theorem<statement<variable<a>, variable<a>>>>);
    };
    template<typename a, typename b>
    using lemma_Sa_plus_b_equals_S_of_a_plus_b = std::conditional_t<std::is_same_v<a, b>,
        lemma_Sa_plus_b_equals_S_of_a_plus_b__implementation_for_identical_variables<a>,
        lemma_Sa_plus_b_equals_S_of_a_plus_b__implementation_for_different_variables<a, b>
    >;
    using prop_SS_of_k_plus_k_equals_S_of_Sk_plus_k = apply_modus_ponens<
        axioms::S_is_a_function<S<sum<variable<k>, variable<k>>>, sum<S<variable<k>>, variable<k>>>,
        apply_modus_ponens<
            axioms::symmetry_of_equality<sum<S<variable<k>>, variable<k>>, S<sum<variable<k>, variable<k>>>>,
            typename lemma_Sa_plus_b_equals_S_of_a_plus_b<k, k>::result
        >
    >;
    using prop_S_of_Sk_plus_k_equals_Sk_plus_Sk = apply_modus_ponens<
        axioms::symmetry_of_equality<sum<S<variable<k>>, S<variable<k>>>, S<sum<S<variable<k>>, variable<k>>>>,
        axioms::a_plus_Sb_is_S_of_a_plus_b<S<variable<k>>, variable<k>>
    >;
    using prop_SS_of_k_plus_k_equals_Sk_plus_Sk = apply_modus_ponens_twice<
        typename lemma_a_equals_b_implies_b_equals_c_implies_a_equals_c<
            S<S<sum<variable<k>, variable<k>>>>,
            S<sum<S<variable<k>>, variable<k>>>,
            sum<S<variable<k>>, S<variable<k>>>
        >::result,
        prop_SS_of_k_plus_k_equals_S_of_Sk_plus_k,
        prop_S_of_Sk_plus_k_equals_Sk_plus_Sk
    >;
    using prop_Sm_equals_SS_of_k_plus_k_implies_Sm_equals_Sk_plus_Sk = apply_conditional_modus_ponens_twice<
        add_hypothesis<equal<S<variable<m>>, S<S<sum<variable<k>, variable<k>>>>>,
            typename lemma_a_equals_b_implies_b_equals_c_implies_a_equals_c<
                S<variable<m>>,
                S<S<sum<variable<k>, variable<k>>>>,
                sum<S<variable<k>>, S<variable<k>>>
            >::result
        >,
        use_library_lemma<
            implication<equal<S<variable<m>>, S<S<sum<variable<k>, variable<k>>>>>, equal<S<variable<m>>, S<S<sum<variable<k>, variable<k>>>>>>
        >,
        add_hypothesis<equal<S<variable<m>>, S<S<sum<variable<k>, variable<k>>>>>, prop_SS_of_k_plus_k_equals_Sk_plus_Sk>
    >;
    using prop_m_equals_S_of_k_plus_k_implies_Sm_equals_Sk_plus_Sk = apply_modus_ponens_twice<
        use_library_lemma<ternary_implication<
            implication<equal<variable<m>, S<sum<variable<k>, variable<k>>>>, equal<S<variable<m>>, S<S<sum<variable<k>, variable<k>>>>>>,
            implication<equal<S<variable<m>>, S<S<sum<variable<k>, variable<k>>>>>, equal<S<variable<m>>, sum<S<variable<k>>, S<variable<k>>>>>,
            implication<equal<variable<m>, S<sum<variable<k>, variable<k>>>>, equal<S<variable<m>>, sum<S<variable<k>>, S<variable<k>>>>>
        >>,
        axioms::S_is_a_function<variable<m>, S<sum<variable<k>, variable<k>>>>,
        prop_Sm_equals_SS_of_k_plus_k_implies_Sm_equals_Sk_plus_Sk
    >;
    static_assert(std::is_same_v<prop_m_equals_S_of_k_plus_k_implies_Sm_equals_Sk_plus_Sk, theorem<
        implication<equal<variable<m>, S<sum<variable<k>, variable<k>>>>, equal<S<variable<m>>, sum<S<variable<k>>, S<variable<k>>>>>
    >>);
    struct l {};
    using prop_m_equals_S_of_k_plus_k_implies_forall_l_Sm_neq_l_plus_l_implies_m_equals_S_of_k_plus_k = propositional::hypothesis_addition<
        equal<variable<m>, S<sum<variable<k>, variable<k>>>>,
        forall<l, negation<equal<S<variable<m>>, sum<variable<l>, variable<l>>>>>
    >;
    using prop_m_equals_S_of_k_plus_k_implies_forall_l_Sm_neq_l_plus_l_implies_Sm_equals_Sk_plus_Sk = apply_conditional_conditional_modus_ponens<
        add_hypothesis<equal<variable<m>, S<sum<variable<k>, variable<k>>>>,
            add_hypothesis<forall<l, negation<equal<S<variable<m>>, sum<variable<l>, variable<l>>>>>,
                prop_m_equals_S_of_k_plus_k_implies_Sm_equals_Sk_plus_Sk
            >
        >,
        prop_m_equals_S_of_k_plus_k_implies_forall_l_Sm_neq_l_plus_l_implies_m_equals_S_of_k_plus_k
    >;
    using prop_m_equals_S_of_k_plus_k_implies_forall_l_Sm_neq_l_plus_l_implies_Sm_neq_Sk_plus_Sk = add_hypothesis<
        equal<variable<m>, S<sum<variable<k>, variable<k>>>>,
        firstorder::apply_universal_instantiation<l, S<variable<k>>,
            forall<l, negation<equal<S<variable<m>>, sum<variable<l>, variable<l>>>>>,
            negation<equal<S<variable<m>>, sum<S<variable<k>>, S<variable<k>>>>>
        >
    >;
    using prop_m_equals_S_of_k_plus_k_implies_exists_l_Sm_equals_l_plus_l = apply_conditional_conditional_modus_ponens<
        prop_m_equals_S_of_k_plus_k_implies_forall_l_Sm_neq_l_plus_l_implies_Sm_neq_Sk_plus_Sk,
        prop_m_equals_S_of_k_plus_k_implies_forall_l_Sm_neq_l_plus_l_implies_Sm_equals_Sk_plus_Sk
    >;
    using prop_m_equals_S_of_k_plus_k_implies_Sm_is_even_wrt_l = prop_m_equals_S_of_k_plus_k_implies_exists_l_Sm_equals_l_plus_l;
    static_assert(std::is_same_v<prop_m_equals_S_of_k_plus_k_implies_Sm_is_even_wrt_l, theorem<
        implication<equal<variable<m>, S<sum<variable<k>, variable<k>>>>, is_even<S<variable<m>>, l>>
    >>);
    using prop__forall_k__m_equals_S_of_k_plus_k_implies_Sm_is_even_wrt_l = unconditionally_apply_universal_generalization<k,
        prop_m_equals_S_of_k_plus_k_implies_Sm_is_even_wrt_l,
        forall<k, implication<equal<variable<m>, S<sum<variable<k>, variable<k>>>>, is_even<S<variable<m>>, l>>>
    >;
    using premise1 = is_odd<variable<m>, k>;
    using prop_premise1_implies_exists_k_Sm_is_even_wrt_l = apply_conditional_modus_ponens<
        split_hypotheses<conditionally_perform_implication_under_existential_quantifier<k,
            equal<variable<m>, S<sum<variable<k>, variable<k>>>>,
            is_even<S<variable<m>>, l>
        >>,
        add_hypothesis<premise1, prop__forall_k__m_equals_S_of_k_plus_k_implies_Sm_is_even_wrt_l>
    >;
    static_assert(std::is_same_v<prop_premise1_implies_exists_k_Sm_is_even_wrt_l, theorem<
        implication<premise1, exists<k, is_even<S<variable<m>>, l>>>
    >>);
    using prop_premise1_implies_Sm_is_even_wrt_l = apply_conditional_modus_ponens<
        add_hypothesis<premise1, try_to_implicationally_remove_vacuous_existential_quantifier<k, is_even<S<variable<m>>, l>>>,
        prop_premise1_implies_exists_k_Sm_is_even_wrt_l
    >;
    static_assert(std::is_same_v<prop_premise1_implies_Sm_is_even_wrt_l, theorem<
        implication<is_odd<variable<m>, k>, is_even<S<variable<m>>, l>>
    >>);
    template<typename a>
    struct temp_template {
        using type = equal<S<variable<m>>, sum<variable<a>, variable<a>>>;
    };
    using prop_Sm_is_even_wrt_l_implies_Sm_is_even_wrt_k = try_to_implicationally_silently_replace_variable_E<l, k, temp_template>;
    using prop_m_is_odd_implies_Sm_is_even = apply_modus_ponens_twice<
        use_library_lemma<ternary_implication<
            implication<is_odd<variable<m>, k>, is_even<S<variable<m>>, l>>,
            implication<is_even<S<variable<m>>, l>, is_even<S<variable<m>>, k>>,
            implication<is_odd<variable<m>, k>, is_even<S<variable<m>>, k>>
        >>,
        prop_premise1_implies_Sm_is_even_wrt_l,
        prop_Sm_is_even_wrt_l_implies_Sm_is_even_wrt_k
    >;
    static_assert(std::is_same_v<prop_m_is_odd_implies_Sm_is_even, theorem<subgoal1>>);

    // almost done!

    using m_is_even = is_even<variable<m>, k>;
    using m_is_odd = is_odd<variable<m>, k>;
    using Sm_is_even = is_even<S<variable<m>>, k>;
    using Sm_is_odd = is_odd<S<variable<m>>, k>;
    using prop_statement_for_m_implies_statement_for_Sm = apply_modus_ponens<
        use_library_lemma<implication<
            conjunction<implication<m_is_even, Sm_is_odd>, implication<m_is_odd, Sm_is_even>>,
            implication<statement_for<variable<m>>, statement_for<S<variable<m>>>>
        >>,
        apply_modus_ponens_twice<
            propositional::conjunction_introduction<implication<m_is_even, Sm_is_odd>, implication<m_is_odd, Sm_is_even>>,
            prop_m_is_even_implies_Sm_is_odd,
            prop_m_is_odd_implies_Sm_is_even
        >
    >;
    using prop_n_is_either_even_or_odd_implies_Sn_is_either_even_or_odd = prop_statement_for_m_implies_statement_for_Sm;  // remember, m = n
    static_assert(std::is_same_v<prop_n_is_either_even_or_odd_implies_Sn_is_either_even_or_odd, theorem<
        implication<statement_for<variable<n>>, statement_for<S<variable<n>>>>
    >>);

    using prop_statement_for_n = apply_modus_ponens_twice<
        axioms::induction<n, statement_for<variable<n>>>,
        prop_0_is_either_even_or_odd,
        prop_n_is_either_even_or_odd_implies_Sn_is_either_even_or_odd
    >;
    static_assert(std::is_same_v<prop_statement_for_n, theorem<
        disjunction<exists<k, equal<variable<n>, sum<variable<k>, variable<k>>>>, exists<k, equal<variable<n>, S<sum<variable<k>, variable<k>>>>>>
    >>);
};


void test2() {
    struct n {};
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
        equal<Zero, sum<Zero, Zero>>>::value);
}