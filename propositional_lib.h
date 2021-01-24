template<typename a, typename b, typename c, typename d>
using quaternary_implication = implication<a, ternary_implication<b, c, d>>;
template<typename a, typename b, typename c, typename d, typename e>
using quinternary_implication = implication<a, quaternary_implication<b, c, d, e>>;
template<typename...>
struct multiary_implication_wrapper {};
template<typename a, typename b>
struct multiary_implication_wrapper<a, b> {
    using result = implication<a, b>;
};
template<typename a, typename b, typename c, typename... etc>
struct multiary_implication_wrapper<a, b, c, etc...> {
    using result = implication<a, typename multiary_implication_wrapper<b, c, etc...>::result>;
};
template<typename... s>
using multiary_implication = typename multiary_implication_wrapper<s...>::result;

template<typename a, typename b, typename c>
using ternary_conjunction = conjunction<conjunction<a, b>, c>;

template<typename, typename>
struct illformed_hypothesis_addition {};
template<typename h, typename th_a>
struct add_hypothesis_t {
    using result = illformed_hypothesis_addition<h, th_a>;
};
template<typename h, typename a>
struct add_hypothesis_t<h, theorem<a>> {
    using th_a = theorem<a>;
    using result = apply_modus_ponens<propositional::hypothesis_addition<a, h>, th_a>;
    static_assert(std::is_same_v<result, theorem<implication<h, a>>>);
};
template<typename h, typename th_a>
using add_hypothesis = typename add_hypothesis_t<h, th_a>::result;

template<typename th_A_implies_B_implies_C, typename th_A, typename th_B>
using apply_modus_ponens_twice = apply_modus_ponens<apply_modus_ponens<th_A_implies_B_implies_C, th_A>, th_B>;

template<typename, typename>
struct illformed_conditional_modus_ponens_application {};
template<typename th_A_implies_B_implies_C, typename th_A_implies_B>
struct conditional_modus_ponens_t {
    using result = illformed_conditional_modus_ponens_application<th_A_implies_B_implies_C, th_A_implies_B>;
};
template<typename A, typename B, typename C>
struct conditional_modus_ponens_t<theorem<ternary_implication<A, B, C>>, theorem<implication<A, B>>> {
    using th_A_implies_B_implies_C = theorem<ternary_implication<A, B, C>>;
    using th_A_implies_B = theorem<implication<A, B>>;
    using result = apply_modus_ponens_twice<
        propositional::conditional_modus_ponens<A, B, C>,
        th_A_implies_B_implies_C,
        th_A_implies_B
    >;
    static_assert(std::is_same_v<result, theorem<implication<A, C>>>);
};
template<typename th_A_implies_B_implies_C, typename th_A_implies_B>
using apply_conditional_modus_ponens = typename conditional_modus_ponens_t<th_A_implies_B_implies_C, th_A_implies_B>::result;
template<typename th_A_implies_B_implies_C, typename th_A_implies_B>
using apply_conditional_mp = apply_conditional_modus_ponens<th_A_implies_B_implies_C, th_A_implies_B>;
template<typename th_A_implies_B_implies_C, typename th_A_implies_B>
using apply_cmp = apply_conditional_modus_ponens<th_A_implies_B_implies_C, th_A_implies_B>;
template<typename th_A_implies_B_implies_C_implies_D, typename th_A_implies_B, typename th_A_implies_C>
using apply_conditional_modus_ponens_twice = apply_conditional_modus_ponens<
    apply_conditional_modus_ponens<th_A_implies_B_implies_C_implies_D, th_A_implies_B>,
    th_A_implies_C
>;
template<typename th_A_implies_B_implies_C_implies_D_implies_E, typename th_A_implies_B, typename th_A_implies_C, typename th_A_implies_D>
using apply_conditional_modus_ponens_thrice = apply_conditional_modus_ponens<
    apply_conditional_modus_ponens_twice<th_A_implies_B_implies_C_implies_D_implies_E, th_A_implies_B, th_A_implies_C>,
    th_A_implies_D
>;

template<typename, typename>
struct illformed_conditional_conditional_modus_ponens_application {};
template<typename th_A_implies_B_implies_C_implies_D, typename th_A_implies_B_implies_C>
struct conditional_conditional_modus_ponens_t {
    using result = illformed_conditional_conditional_modus_ponens_application<th_A_implies_B_implies_C_implies_D, th_A_implies_B_implies_C>;
};
template<typename A, typename B, typename C, typename D>
struct conditional_conditional_modus_ponens_t<theorem<quaternary_implication<A, B, C, D>>, theorem<ternary_implication<A, B, C>>> {
    using th_A_implies_B_implies_C_implies_D = theorem<multiary_implication<A, B, C, D>>;
    using th_A_implies_B_implies_C = theorem<ternary_implication<A, B, C>>;
    using prop__A__implies__B_implies_C_implies_D__implies__B_implies_C__implies__B_implies_D
        = add_hypothesis<A, propositional::conditional_modus_ponens<B, C, D>>;
    using prop__A__implies__B_implies_C__implies__B_implies_D = apply_conditional_modus_ponens<
        prop__A__implies__B_implies_C_implies_D__implies__B_implies_C__implies__B_implies_D,
        th_A_implies_B_implies_C_implies_D
    >;
    using prop_A_implies_B_implies_D = apply_conditional_modus_ponens<
        prop__A__implies__B_implies_C__implies__B_implies_D,
        th_A_implies_B_implies_C
    >;
    using result = prop_A_implies_B_implies_D;
    static_assert(std::is_same_v<prop_A_implies_B_implies_D, theorem<ternary_implication<A, B, D>>>);
};
template<typename th_A_implies_B_implies_C_implies_D, typename th_A_implies_B_implies_C>
using apply_conditional_conditional_modus_ponens
    = typename conditional_conditional_modus_ponens_t<th_A_implies_B_implies_C_implies_D, th_A_implies_B_implies_C>::result;
template<typename th_A_implies_B_implies_C_implies_D, typename th_A_implies_B_implies_C>
using apply_conditional_conditional_mp
    = typename conditional_conditional_modus_ponens_t<th_A_implies_B_implies_C_implies_D, th_A_implies_B_implies_C>::result;
template<typename th_A_implies_B_implies_C_implies_D, typename th_A_implies_B_implies_C>
using apply_ccmp = typename conditional_conditional_modus_ponens_t<th_A_implies_B_implies_C_implies_D, th_A_implies_B_implies_C>::result;
template<typename th_A_implies_B_implies_C_implies_D_implies_E, typename th_A_implies_B_implies_C, typename th_A_implies_B_implies_D>
using apply_conditional_conditional_modus_ponens_twice = apply_conditional_conditional_modus_ponens<
    apply_conditional_conditional_modus_ponens<th_A_implies_B_implies_C_implies_D_implies_E, th_A_implies_B_implies_C>,
    th_A_implies_B_implies_D
>;

template<typename, typename>
struct illformed_conditional_conditional_conditional_modus_ponens_application {};
template<typename th_A_implies_B_implies_C_implies_D_implies_E, typename th_A_implies_B_implies_C_implies_D>
struct conditional_conditional_conditional_modus_ponens_t {
    using result = illformed_conditional_conditional_conditional_modus_ponens_application<
        th_A_implies_B_implies_C_implies_D_implies_E, th_A_implies_B_implies_C_implies_D
    >;
};
template<typename A, typename B, typename C, typename D, typename E>
struct conditional_conditional_conditional_modus_ponens_t<theorem<quinternary_implication<A, B, C, D, E>>,
                theorem<quaternary_implication<A, B, C, D>>> {
    using th_A_implies_B_implies_C_implies_D_implies_E = theorem<multiary_implication<A, B, C, D, E>>;
    using th_A_implies_B_implies_C_implies_D = theorem<multiary_implication<A, B, C, D>>;
    using prop__A__implies__B__implies__C_implies_D_implies_E__implies__C_implies_D__implies__C_implies_E
        = add_hypothesis<A, add_hypothesis<B, propositional::conditional_modus_ponens<C, D, E>>>;
    using prop__A__implies__B__implies__C_implies_D__implies__C_implies_E = apply_conditional_conditional_modus_ponens<
        prop__A__implies__B__implies__C_implies_D_implies_E__implies__C_implies_D__implies__C_implies_E,
        th_A_implies_B_implies_C_implies_D_implies_E
    >;
    using prop_A_implies_B_implies_C_implies_E = apply_conditional_conditional_modus_ponens<
        prop__A__implies__B__implies__C_implies_D__implies__C_implies_E,
        th_A_implies_B_implies_C_implies_D
    >;
    using result = prop_A_implies_B_implies_C_implies_E;
    static_assert(std::is_same_v<result, theorem<multiary_implication<A, B, C, E>>>);
};
template<typename th_A_implies_B_implies_C_implies_D_implies_E, typename th_A_implies_B_implies_C_implies_D>
using apply_conditional_conditional_conditional_modus_ponens = typename conditional_conditional_conditional_modus_ponens_t<
    th_A_implies_B_implies_C_implies_D_implies_E,
    th_A_implies_B_implies_C_implies_D
>::result;
template<typename th_A_implies_B_implies_C_implies_D_implies_E, typename th_A_implies_B_implies_C_implies_D>
using apply_cccmp = typename conditional_conditional_conditional_modus_ponens_t<
    th_A_implies_B_implies_C_implies_D_implies_E,
    th_A_implies_B_implies_C_implies_D
>::result;
template<typename th_A_implies_B_implies_C_implies_D_implies_E_implies_F, typename th_A_implies_B_implies_C_implies_D,
        typename th_A_implies_B_implies_C_implies_E>
using apply_cccmp_twice = apply_cccmp<
    apply_cccmp<th_A_implies_B_implies_C_implies_D_implies_E_implies_F, th_A_implies_B_implies_C_implies_D>,
    th_A_implies_B_implies_C_implies_E
>;
// probably a template for auto-generating these proofs should be written instead


template<typename desire>
struct use_library_lemma_t {
    //static_assert(false, "no such lemma");
    static_assert(!std::is_same_v<desire, desire>, "no such lemma");
    // what the hell: the C++ Standard seems not to define compiler's behavior for this case
};
template<typename desire>
using use_library_lemma = typename use_library_lemma_t<desire>::result;
// usage: you call for use_conditional_library_lemma<whatever>, and it either returns theorem<whatever> if a lemma in the library can be applied,
//     or fails with "no such lemma" printed (hopefully)
template<typename H, typename desire>
struct use_library_lemma_t<implication<H, desire>> : use_library_lemma_t<desire> {};


template<typename a, typename b, typename c>
struct lemma_a_implies_b_implies_c_implies_a {
    using prop_a_implies_b_implies_a = propositional::hypothesis_addition<a, b>;
    using prop_a_implies_b_implies_a_implies_c_implies_a = add_hypothesis<a, add_hypothesis<b, propositional::hypothesis_addition<a, c>>>;
    using prop_a_implies_b_implies_c_implies_a = apply_conditional_conditional_modus_ponens<
        prop_a_implies_b_implies_a_implies_c_implies_a,
        prop_a_implies_b_implies_a
    >;
    using result = prop_a_implies_b_implies_c_implies_a;
    static_assert(std::is_same_v<result, theorem<multiary_implication<a, b, c, a>>>);
};
template<typename a, typename b, typename c>
struct use_library_lemma_t<quaternary_implication<a, b, c, a>> {
    using result = typename lemma_a_implies_b_implies_c_implies_a<a, b, c>::result;
};


template<typename h1, typename h2, typename prop>
struct implicational_merging_hypotheses {
    using premise = ternary_implication<h1, h2, prop>;
    using prop_premise_implies_h1_and_h2_implies_h1_implies_h2_implies_prop = propositional::hypothesis_addition<premise, conjunction<h1, h2>>;
    using prop_premise_implies_h1_and_h2_implies_h1 = add_hypothesis<premise, propositional::left_conjunction_elimination<h1, h2>>;
    using prop_premise_implies_h1_and_h2_implies_h2_implies_prop = apply_conditional_conditional_modus_ponens<
        prop_premise_implies_h1_and_h2_implies_h1_implies_h2_implies_prop,
        prop_premise_implies_h1_and_h2_implies_h1
    >;
    using prop_premise_implies_h1_and_h2_implies_h2 = add_hypothesis<premise, propositional::right_conjunction_elimination<h1, h2>>;
    using prop_premise_implies_h1_and_h2_implies_prop = apply_conditional_conditional_modus_ponens<
        prop_premise_implies_h1_and_h2_implies_h2_implies_prop,
        prop_premise_implies_h1_and_h2_implies_h2
    >;
    using result = prop_premise_implies_h1_and_h2_implies_prop;
    static_assert(std::is_same_v<result, theorem<implication<ternary_implication<h1, h2, prop>, implication<conjunction<h1, h2>, prop>>>>);
};
template<typename th_h1_implies_h2_implies_prop>
struct merge_hypotheses_t {};
template<typename h1, typename h2, typename prop>
struct merge_hypotheses_t<theorem<ternary_implication<h1, h2, prop>>> {
    using th_h1_implies_h2_implies_prop = theorem<ternary_implication<h1, h2, prop>>;
    using result = apply_modus_ponens<
        typename implicational_merging_hypotheses<h1, h2, prop>::result,
        th_h1_implies_h2_implies_prop
    >;
    static_assert(std::is_same_v<result, theorem<implication<conjunction<h1, h2>, prop>>>);
};
template<typename th_h1_implies_h2_implies_prop>
using merge_hypotheses = typename merge_hypotheses_t<th_h1_implies_h2_implies_prop>::result;
template<typename h1, typename h2, typename prop>
struct use_library_lemma_t<implication<ternary_implication<h1, h2, prop>, implication<conjunction<h1, h2>, prop>>> {
    using result = typename implicational_merging_hypotheses<h1, h2, prop>::result;
};

template<typename h1, typename h2, typename prop>
struct implicational_splitting_hypotheses {
    using premise = implication<conjunction<h1, h2>, prop>;
    using prop_premise_implies_h1_implies_h2_implies_h1_and_h2_implies_prop = use_library_lemma<multiary_implication<premise, h1, h2, premise>>;
    static_assert(std::is_same_v<prop_premise_implies_h1_implies_h2_implies_h1_and_h2_implies_prop, theorem<
        multiary_implication<premise, h1, h2, conjunction<h1, h2>, prop>
    >>);
    using prop_premise_implies_h1_implies_h2_implies_h1_and_h2
        = add_hypothesis<premise, propositional::conjunction_introduction<h1, h2>>;
    using prop_premise_implies_h1_implies_h2_implies_prop = apply_conditional_conditional_conditional_modus_ponens<
        prop_premise_implies_h1_implies_h2_implies_h1_and_h2_implies_prop,
        prop_premise_implies_h1_implies_h2_implies_h1_and_h2
    >;
    using result = prop_premise_implies_h1_implies_h2_implies_prop;
    static_assert(std::is_same_v<result, theorem<implication<implication<conjunction<h1, h2>, prop>, ternary_implication<h1, h2, prop>>>>);
};
template<typename th_h1_and_h2_implies_prop>
struct split_hypotheses_t {};
template<typename h1, typename h2, typename prop>
struct split_hypotheses_t<theorem<implication<conjunction<h1, h2>, prop>>> {
    using th_h1_and_h2_implies_prop = theorem<implication<conjunction<h1, h2>, prop>>;
    using result = apply_modus_ponens<
        typename implicational_splitting_hypotheses<h1, h2, prop>::result,
        th_h1_and_h2_implies_prop
    >;
    static_assert(std::is_same_v<result, theorem<ternary_implication<h1, h2, prop>>>);
};
template<typename th_h1_and_h2_implies_prop>
using split_hypotheses = typename split_hypotheses_t<th_h1_and_h2_implies_prop>::result;
template<typename h1, typename h2, typename prop>
struct use_library_lemma_t<implication<implication<conjunction<h1, h2>, prop>, ternary_implication<h1, h2, prop>>> {
    using result = typename implicational_splitting_hypotheses<h1, h2, prop>::result;
};

template<typename h1, typename h2, typename prop>
struct implicational_swapping_hypotheses_in_implication {
    using premise = ternary_implication<h1, h2, prop>;
    using prop_premise_implies_h2_implies_h1_implies_h1_implies_h2_implies_prop
        = use_library_lemma<multiary_implication<premise, h2, h1, premise>>;
    using prop_premise_implies_h2_implies_h1_implies_h1 = add_hypothesis<premise,
        add_hypothesis<h2, use_library_lemma<implication<h1, h1>>>
    >;
    using prop_premise_implies_h2_implies_h1_implies_h2_implies_prop = apply_conditional_conditional_conditional_modus_ponens<
        prop_premise_implies_h2_implies_h1_implies_h1_implies_h2_implies_prop,
        prop_premise_implies_h2_implies_h1_implies_h1
    >;
    using prop_premise_implies_h2_implies_h1_implies_h2 = add_hypothesis<premise, propositional::hypothesis_addition<h2, h1>>;
    using prop_premise_implies_h2_implies_h1_implies_prop = apply_conditional_conditional_conditional_modus_ponens<
        prop_premise_implies_h2_implies_h1_implies_h2_implies_prop,
        prop_premise_implies_h2_implies_h1_implies_h2
    >;
    using result = prop_premise_implies_h2_implies_h1_implies_prop;
    static_assert(std::is_same_v<result, theorem<implication<ternary_implication<h1, h2, prop>, ternary_implication<h2, h1, prop>>>>);
};
template<typename th_h1_and_h2_implies_prop>
struct swap_hypotheses_in_implication_t {};
template<typename h1, typename h2, typename prop>
struct swap_hypotheses_in_implication_t<theorem<ternary_implication<h1, h2, prop>>> {
    using th_h1_implies_h2_implies_prop = theorem<ternary_implication<h1, h2, prop>>;
    using result = apply_modus_ponens<
        typename implicational_swapping_hypotheses_in_implication<h1, h2, prop>::result,
        th_h1_implies_h2_implies_prop
    >;
    static_assert(std::is_same_v<result, theorem<ternary_implication<h2, h1, prop>>>);
};
template<typename th_h1_and_h2_implies_prop>
using swap_hypotheses_in_implication = typename swap_hypotheses_in_implication_t<th_h1_and_h2_implies_prop>::result;
template<typename h1, typename h2, typename prop>
struct use_library_lemma_t<implication<ternary_implication<h1, h2, prop>, ternary_implication<h2, h1, prop>>> {
    using result = typename implicational_swapping_hypotheses_in_implication<h1, h2, prop>::result;
};

template<typename h1, typename h2, typename prop>
struct implicational_swapping_hypotheses_in_conjunction {
    using premise = implication<conjunction<h1, h2>, prop>;
    using prop_premise_implies_h1_implies_h2_implies_prop = use_library_lemma<implication<premise, ternary_implication<h1, h2, prop>>>;
    using prop__h1_implies_h2_implies_prop__implies__h2_implies_h1_implies_prop = use_library_lemma<
        implication<ternary_implication<h1, h2, prop>, ternary_implication<h2, h1, prop>>
    >;
    using prop__premise__implies__h1_implies_h2_implies_prop__implies__h2_implies_h1_implies_prop
        = add_hypothesis<premise, prop__h1_implies_h2_implies_prop__implies__h2_implies_h1_implies_prop>;
    using prop_premise_implies_h2_implies_h1_implies_prop = apply_conditional_modus_ponens<
        prop__premise__implies__h1_implies_h2_implies_prop__implies__h2_implies_h1_implies_prop,
        prop_premise_implies_h1_implies_h2_implies_prop
    >;
    using prop_premise_implies_h2_and_h1_implies_prop = apply_conditional_modus_ponens<
        add_hypothesis<premise, use_library_lemma<implication<ternary_implication<h2, h1, prop>, implication<conjunction<h2, h1>, prop>>>>,
        prop_premise_implies_h2_implies_h1_implies_prop
    >;
    using result = prop_premise_implies_h2_and_h1_implies_prop;
    static_assert(std::is_same_v<result, theorem<implication<implication<conjunction<h1, h2>, prop>, implication<conjunction<h2, h1>, prop>>>>);
};
template<typename th_h1_and_h2_implies_prop>
struct swap_hypotheses_in_conjunction_t {};
template<typename h1, typename h2, typename prop>
struct swap_hypotheses_in_conjunction_t<implication<conjunction<h1, h2>, prop>> {
    using th_h1_and_h2_implies_prop = theorem<implication<conjunction<h1, h2>, prop>>;
    using result = apply_modus_ponens<
        typename implicational_swapping_hypotheses_in_conjunction<h1, h2, prop>::result,
        th_h1_and_h2_implies_prop
    >;
    static_assert(std::is_same_v<result, theorem<implication<conjunction<h2, h1>, prop>>>);
};
template<typename th_h1_and_h2_implies_prop>
using swap_hypotheses_in_conjunction = typename swap_hypotheses_in_conjunction_t<th_h1_and_h2_implies_prop>::result;
template<typename h1, typename h2, typename prop>
struct use_library_lemma_t<implication<implication<conjunction<h1, h2>, prop>, implication<conjunction<h2, h1>, prop>>> {
    using result = typename implicational_swapping_hypotheses_in_conjunction<h1, h2, prop>::result;
};

template<typename h1, typename h2, typename prop>
struct implicational_swapping_hypotheses_in_disjunction {
    using premise = implication<disjunction<h1, h2>, prop>;
    using prop_premise_implies_h1_implies_prop = apply_conditional_modus_ponens_twice<
        add_hypothesis<premise, use_library_lemma<ternary_implication<
            implication<h1, disjunction<h1, h2>>,
            implication<disjunction<h1, h2>, prop>,
            implication<h1, prop>
        >>>,
        add_hypothesis<premise, propositional::left_disjunction_introduction<h1, h2>>,
        use_library_lemma<implication<premise, premise>>
    >;
    using prop_premise_implies_h2_implies_prop = apply_conditional_modus_ponens_twice<
        add_hypothesis<premise, use_library_lemma<ternary_implication<
            implication<h2, disjunction<h1, h2>>,
            implication<disjunction<h1, h2>, prop>,
            implication<h2, prop>
        >>>,
        add_hypothesis<premise, propositional::right_disjunction_introduction<h1, h2>>,
        use_library_lemma<implication<premise, premise>>
    >;
    using prop_premise_implies_h2_or_h1_implies_prop = apply_conditional_modus_ponens_twice<
        add_hypothesis<premise, propositional::disjunction_elimination<h2, h1, prop>>,
        prop_premise_implies_h2_implies_prop,
        prop_premise_implies_h1_implies_prop
    >;
    using result = prop_premise_implies_h2_or_h1_implies_prop;
    static_assert(std::is_same_v<result, theorem<
        implication<implication<disjunction<h1, h2>, prop>, implication<disjunction<h2, h1>, prop>>
    >>);
};
template<typename th_h1_or_h2_implies_prop>
struct swap_hypotheses_in_disjunction_t {};
template<typename h1, typename h2, typename prop>
struct swap_hypotheses_in_disjunction_t<theorem<implication<disjunction<h1, h2>, prop>>> {
    using th_h1_or_h2_implies_prop = theorem<implication<disjunction<h1, h2>, prop>>;
    using result = apply_modus_ponens<
        typename implicational_swapping_hypotheses_in_disjunction<h1, h2, prop>::result,
        th_h1_or_h2_implies_prop
    >;
    static_assert(std::is_same_v<result, theorem<implication<disjunction<h2, h1>, prop>>>);
};
template<typename th_h1_or_h2_implies_prop>
using swap_hypotheses_in_disjunction = typename swap_hypotheses_in_disjunction_t<th_h1_or_h2_implies_prop>::result;
template<typename h1, typename h2, typename prop>
struct use_library_lemma_t<implication<implication<disjunction<h1, h2>, prop>, implication<disjunction<h2, h1>, prop>>> {
    using result = typename implicational_swapping_hypotheses_in_disjunction<h1, h2, prop>::result;
};

/* probably something like implicational_anything_in_implication should be automatically constructed for any desired hypothesis substitution
on the basis of the corresponding propositional theorem */


template<typename a>
struct lemma_a_implies_a {
    using b = implication<a, a>;
    using prop_a_implies_b_implies_a = propositional::hypothesis_addition<a, b>;
    using prop_a_implies_b = propositional::hypothesis_addition<a, a>;
    using prop_a_implies_a = apply_conditional_modus_ponens<prop_a_implies_b_implies_a, prop_a_implies_b>;
    using result = prop_a_implies_a;
    static_assert(std::is_same_v<result, theorem<implication<a, a>>>);
};
template<typename a>
struct use_library_lemma_t<implication<a, a>> {
    using result = typename lemma_a_implies_a<a>::result;
};

using th_true = use_library_lemma<True>;
static_assert(std::is_same_v<th_true, theorem<True>>);

template<typename a, typename b, typename c>
struct lemma__a_implies_b__implies__b_implies_c__implies__a_implies_c {
    using premise = conjunction<implication<a, b>, implication<b, c>>;
    using prop_premise_implies_b_implies_c = propositional::right_conjunction_elimination<implication<a, b>, implication<b, c>>;
    using prop_premise_implies_a_implies_b_implies_c = apply_conditional_modus_ponens<
        add_hypothesis<premise, propositional::hypothesis_addition<implication<b, c>, a>>,
        prop_premise_implies_b_implies_c
    >;
    using prop_premise_implies_a_implies_b = propositional::left_conjunction_elimination<implication<a, b>, implication<b, c>>;
    using prop_premise_implies_a_implies_c = apply_conditional_conditional_modus_ponens<
        prop_premise_implies_a_implies_b_implies_c,
        prop_premise_implies_a_implies_b
    >;
    using prop__a_implies_b__implies__b_implies_c__implies__a_implies_c = split_hypotheses<prop_premise_implies_a_implies_c>;
    using result = prop__a_implies_b__implies__b_implies_c__implies__a_implies_c;
    static_assert(std::is_same_v<result, theorem<ternary_implication<implication<a, b>, implication<b, c>, implication<a, c>>>>);
};
template<typename a, typename b, typename c>
struct use_library_lemma_t<ternary_implication<implication<a, b>, implication<b, c>, implication<a, c>>> {
    using result = typename lemma__a_implies_b__implies__b_implies_c__implies__a_implies_c<a, b, c>::result;
};

template<typename a, typename b, typename c>
struct lemma__a_implies_b__and__a_implies_c__implies__a_implies_b_and_c {
    using premise = conjunction<implication<a, b>, implication<a, c>>;
    using prop_premise_implies_a_implies_a = add_hypothesis<premise, use_library_lemma<implication<a, a>>>;
    using prop__premise__implies__a__implies__a_implies_b__and__a_implies_c__implies__a_implies_b = add_hypothesis<premise, add_hypothesis<a,
        propositional::left_conjunction_elimination<implication<a, b>, implication<a, c>>
    >>;
    using prop__premise__implies__a__implies__a_implies_b__and__a_implies_c = propositional::hypothesis_addition<premise, a>;
    using prop_premise_implies_a_implies_a_implies_b = apply_conditional_conditional_modus_ponens<
        prop__premise__implies__a__implies__a_implies_b__and__a_implies_c__implies__a_implies_b,
        prop__premise__implies__a__implies__a_implies_b__and__a_implies_c
    >;
    using prop_premise_implies_a_implies_b = apply_conditional_conditional_modus_ponens<
        prop_premise_implies_a_implies_a_implies_b,
        prop_premise_implies_a_implies_a
    >;
    using prop__premise__implies__a__implies__a_implies_b__and__a_implies_c__implies__a_implies_c = add_hypothesis<premise, add_hypothesis<a,
        propositional::right_conjunction_elimination<implication<a, b>, implication<a, c>>
    >>;
    using prop_premise_implies_a_implies_a_implies_c = apply_conditional_conditional_modus_ponens<
        prop__premise__implies__a__implies__a_implies_b__and__a_implies_c__implies__a_implies_c,
        prop__premise__implies__a__implies__a_implies_b__and__a_implies_c
    >;
    using prop_premise_implies_a_implies_c = apply_conditional_conditional_modus_ponens<
        prop_premise_implies_a_implies_a_implies_c,
        prop_premise_implies_a_implies_a
    >;
    using prop_premise_implies_a_implies_b_implies_c_implies_b_and_c = add_hypothesis<premise, add_hypothesis<a,
        propositional::conjunction_introduction<b, c>
    >>;
    using prop_premise_implies_a_implies_b_and_c = apply_conditional_conditional_modus_ponens<
        apply_conditional_conditional_modus_ponens<
            prop_premise_implies_a_implies_b_implies_c_implies_b_and_c,
            prop_premise_implies_a_implies_b
        >,
        prop_premise_implies_a_implies_c
    >;
    using result = prop_premise_implies_a_implies_b_and_c;
    static_assert(std::is_same_v<result, theorem<
        implication<conjunction<implication<a, b>, implication<a, c>>, implication<a, conjunction<b, c>>>
    >>);
};
template<typename a, typename b, typename c>
struct use_library_lemma_t<implication<conjunction<implication<a, b>, implication<a, c>>, implication<a, conjunction<b, c>>>> {
    using result = typename lemma__a_implies_b__and__a_implies_c__implies__a_implies_b_and_c<a, b, c>::result;
};

template<typename a>
struct lemma_a_and_not_a_implies_false {
    using premise = conjunction<a, negation<a>>;
    using prop_premise_implies_false = apply_conditional_modus_ponens<
        propositional::right_conjunction_elimination<a, negation<a>>,
        propositional::left_conjunction_elimination<a, negation<a>>
    >;
    using result = prop_premise_implies_false;
    static_assert(std::is_same_v<result, theorem<implication<conjunction<a, negation<a>>, False>>>);
};
template<typename a>
struct use_library_lemma_t<implication<conjunction<a, negation<a>>, False>> {
    using result = typename lemma_a_and_not_a_implies_false<a>::result;
};

template<typename a, typename b>
struct lemma__a_implies_b__and__a_implies_not_b__implies__not_a {
    using premise = conjunction<implication<a, b>, implication<a, negation<b>>>;
    using prop_premise_implies_a_implies_b = propositional::left_conjunction_elimination<implication<a, b>, implication<a, negation<b>>>;
    using prop_premise_implies_a_implies_not_b = propositional::right_conjunction_elimination<implication<a, b>, implication<a, negation<b>>>;
    using prop_premise_implies_a_implies_false = apply_conditional_conditional_modus_ponens<
        add_hypothesis<premise, add_hypothesis<a, use_library_lemma<implication<conjunction<b, negation<b>>, False>>>>,
        apply_conditional_conditional_modus_ponens<
            apply_conditional_conditional_modus_ponens<
                add_hypothesis<premise, add_hypothesis<a, propositional::conjunction_introduction<b, negation<b>>>>,
                prop_premise_implies_a_implies_b
            >,
            prop_premise_implies_a_implies_not_b
        >
    >;
    using result = prop_premise_implies_a_implies_false;
    static_assert(std::is_same_v<result, theorem<implication<conjunction<implication<a, b>, implication<a, negation<b>>>, negation<a>>>>);
};
template<typename a, typename b>
struct use_library_lemma_t<implication<conjunction<implication<a, b>, implication<a, negation<b>>>, negation<a>>> {
    using result = typename lemma__a_implies_b__and__a_implies_not_b__implies__not_a<a, b>::result;
};

template<typename a>
struct lemma_a_implies_not_not_a {
    using prop_a_implies_not_a_implies_a = propositional::hypothesis_addition<a, negation<a>>;
    using prop_a_implies_not_a_implies_a_implies_false = add_hypothesis<a, use_library_lemma<implication<negation<a>, negation<a>>>>;
    using prop_a_implies_not_a_implies_false = apply_conditional_conditional_modus_ponens<
        prop_a_implies_not_a_implies_a_implies_false,
        prop_a_implies_not_a_implies_a
    >;
    using result = prop_a_implies_not_a_implies_false;
    static_assert(std::is_same_v<result, theorem<implication<a, negation<negation<a>>>>>);
};
template<typename a>
struct use_library_lemma_t<implication<a, negation<negation<a>>>> {
    using result = typename lemma_a_implies_not_not_a<a>::result;
};

template<typename a, typename b, typename c>
struct left_ternary_conjunction_elimination {
    using result = apply_modus_ponens_twice<
        use_library_lemma<ternary_implication<
            implication<ternary_conjunction<a, b, c>, conjunction<a, b>>,
            implication<conjunction<a, b>, a>,
            implication<ternary_conjunction<a, b, c>, a>
        >>,
        propositional::left_conjunction_elimination<conjunction<a, b>, c>,
        propositional::left_conjunction_elimination<a, b>
    >;
    static_assert(std::is_same_v<result, theorem<implication<ternary_conjunction<a, b, c>, a>>>);
};
template<typename a, typename b, typename c>
struct use_library_lemma_t<implication<ternary_conjunction<a, b, c>, a>> {
    using result = typename left_ternary_conjunction_elimination<a, b, c>::result;
};

template<typename a, typename b, typename c>
struct middle_ternary_conjunction_elimination {
    using result = apply_modus_ponens_twice<
        use_library_lemma<ternary_implication<
            implication<ternary_conjunction<a, b, c>, conjunction<a, b>>,
            implication<conjunction<a, b>, b>,
            implication<ternary_conjunction<a, b, c>, b>
        >>,
        propositional::left_conjunction_elimination<conjunction<a, b>, c>,
        propositional::right_conjunction_elimination<a, b>
    >;
    static_assert(std::is_same_v<result, theorem<implication<ternary_conjunction<a, b, c>, b>>>);
};
template<typename a, typename b, typename c>
struct use_library_lemma_t<implication<ternary_conjunction<a, b, c>, b>> {
    using result = typename middle_ternary_conjunction_elimination<a, b, c>::result;
};

template<typename a, typename b, typename c>
struct right_ternary_conjunction_elimination {
    using result = propositional::right_conjunction_elimination<conjunction<a, b>, c>;
    static_assert(std::is_same_v<result, theorem<implication<ternary_conjunction<a, b, c>, c>>>);
};
template<typename a, typename b, typename c>
struct use_library_lemma_t<implication<ternary_conjunction<a, b, c>, c>> {
    using result = typename right_ternary_conjunction_elimination<a, b, c>::result;
};

template<typename a>
struct lemma__true_implies_a__implies__a {
    using premise = implication<True, a>;
    using premise_implies_a = apply_conditional_modus_ponens<
        use_library_lemma<implication<premise, premise>>,
        add_hypothesis<premise, th_true>
    >;
    using result = premise_implies_a;
    static_assert(std::is_same_v<result, theorem<implication<implication<True, a>, a>>>);
};
template<typename a>
struct use_library_lemma_t<implication<implication<True, a>, a>> {
    using result = typename lemma__true_implies_a__implies__a<a>::result;
};

template<typename a, typename b, typename c>
struct lemma__a_implies_b_implies_c__implies__a_implies_not_c_implies_not_b {
    using premise = ternary_implication<a, b, c>;
    using prop_premise_implies_a_implies_b_implies_c = use_library_lemma<implication<premise, premise>>;
    using prop__premise__implies__b_implies_c__implies__not_c_implies_not_b = add_hypothesis<premise,
        use_library_lemma<implication<implication<b, c>, implication<negation<c>, negation<b>>>>
    >;
    using premise_implies_a_implies_not_c_implies_not_b = apply_conditional_modus_ponens_twice<
        add_hypothesis<premise, use_library_lemma<ternary_implication<
            implication<a, implication<b, c>>,
            implication<implication<b, c>, implication<negation<c>, negation<b>>>,
            implication<a, implication<negation<c>, negation<b>>>
        >>>,
        prop_premise_implies_a_implies_b_implies_c,
        prop__premise__implies__b_implies_c__implies__not_c_implies_not_b
    >;
    using result = premise_implies_a_implies_not_c_implies_not_b;
    static_assert(std::is_same_v<result, theorem<implication<ternary_implication<a, b, c>, ternary_implication<a, negation<c>, negation<b>>>>>);
};
template<typename a, typename b, typename c>
struct use_library_lemma_t<implication<ternary_implication<a, b, c>, ternary_implication<a, negation<c>, negation<b>>>> {
    using result = typename lemma__a_implies_b_implies_c__implies__a_implies_not_c_implies_not_b<a, b, c>::result;
};

template<typename a, typename b>
struct lemma__a_or_b__and__not_a__implies__b {
    using premise = conjunction<disjunction<a, b>, negation<a>>;
    using prop_premise_implies_a_implies_b = apply_conditional_modus_ponens_twice<
        add_hypothesis<premise, use_library_lemma<ternary_implication<implication<a, False>, implication<False, b>, implication<a, b>>>>,
        propositional::right_conjunction_elimination<disjunction<a, b>, negation<a>>,
        add_hypothesis<premise, propositional::false_implies_anything<b>>
    >;
    using prop_premise_implies_b_implies_b = add_hypothesis<premise, use_library_lemma<implication<b, b>>>;
    using prop_premise_implies_a_or_b_implies_b = apply_conditional_modus_ponens_twice<
        add_hypothesis<premise, propositional::disjunction_elimination<a, b, b>>,
        prop_premise_implies_a_implies_b,
        prop_premise_implies_b_implies_b
    >;
    using prop_premise_implies_b = apply_conditional_modus_ponens<
        prop_premise_implies_a_or_b_implies_b,
        propositional::left_conjunction_elimination<disjunction<a, b>, negation<a>>
    >;
    using result = prop_premise_implies_b;
    static_assert(std::is_same_v<result, theorem<implication<premise, b>>>);
};
template<typename a, typename b>
struct use_library_lemma_t<implication<conjunction<disjunction<a, b>, negation<a>>, b>> {
    using result = typename lemma__a_or_b__and__not_a__implies__b<a, b>::result;
};

template<typename a, typename b>
struct lemma__a_or_b__and__not_b__implies__a {
    using prop__b_or_a__and__not_b__implies__a = use_library_lemma<implication<conjunction<disjunction<b, a>, negation<b>>, a>>;
    using prop_b_or_a_implies_not_b_implies_a = split_hypotheses<prop__b_or_a__and__not_b__implies__a>;
    using prop_a_or_b_implies_not_b_implies_a = swap_hypotheses_in_disjunction<prop_b_or_a_implies_not_b_implies_a>;
    using prop__a_or_b__and__not_b__implies__a = merge_hypotheses<prop_a_or_b_implies_not_b_implies_a>;
    using result = prop__a_or_b__and__not_b__implies__a;
    static_assert(std::is_same_v<result, theorem<implication<conjunction<disjunction<a, b>, negation<b>>, a>>>);
};
template<typename a, typename b>
struct use_library_lemma_t<implication<conjunction<disjunction<a, b>, negation<b>>, a>> {
    using result = typename lemma__a_or_b__and__not_b__implies__a<a, b>::result;
};

template<typename a>
struct classical_lemma_not_not_a_implies_a {
    static_assert(propositional::allow_law_of_excluded_middle);
    using not_a = negation<a>;
    using not_not_a = negation<not_a>;
    using premise = not_not_a;
    using prop_premise_implies_a_or_not_a = add_hypothesis<premise, propositional::law_of_excluded_middle<a>>;
    using prop_premise_implies_not_not_a = use_library_lemma<implication<not_not_a, not_not_a>>;
    using prop_premise_implies_a = apply_conditional_modus_ponens<
        add_hypothesis<premise, use_library_lemma<implication<conjunction<disjunction<a, not_a>, not_not_a>, a>>>,
        apply_conditional_modus_ponens_twice<
            add_hypothesis<premise, propositional::conjunction_introduction<disjunction<a, not_a>, not_not_a>>,
            prop_premise_implies_a_or_not_a,
            prop_premise_implies_not_not_a
        >
    >;
    using result = prop_premise_implies_a;
    static_assert(std::is_same_v<result, theorem<implication<negation<negation<a>>, a>>>);
};
template<typename a>
struct use_library_lemma_t<implication<negation<negation<a>>, a>> {
    using result = typename classical_lemma_not_not_a_implies_a<a>::result;
};

template<typename a, typename b>
struct lemma_a_or_b_implies_b_or_a {
    using prop_a_implies_b_or_a = propositional::right_disjunction_introduction<b, a>;
    using prop_b_implies_b_or_a = propositional::left_disjunction_introduction<b, a>;
    using prop_a_or_b_implies_b_or_a = apply_modus_ponens_twice<
        propositional::disjunction_elimination<a, b, disjunction<b, a>>,
        prop_a_implies_b_or_a,
        prop_b_implies_b_or_a
    >;
    using result = prop_a_or_b_implies_b_or_a;
    static_assert(std::is_same_v<result, theorem<implication<disjunction<a, b>, disjunction<b, a>>>>);
};
template<typename a, typename b>
struct use_library_lemma_t<implication<disjunction<a, b>, disjunction<b, a>>> {
    using result = typename lemma_a_or_b_implies_b_or_a<a, b>::result;
};

template<typename a, typename b, typename c, typename d>
struct lemma__a_implies_c__and__b_implies_d__implies__a_or_b_implies_c_or_d {
    using premise = conjunction<implication<a, c>, implication<b, d>>;
    using prop_premise_implies_a_implies_c_or_d = apply_conditional_conditional_modus_ponens<
        add_hypothesis<premise, add_hypothesis<a, propositional::left_disjunction_introduction<c, d>>>,
        propositional::left_conjunction_elimination<implication<a, c>, implication<b, d>>
    >;
    using prop_premise_implies_b_implies_c_or_d = apply_conditional_conditional_modus_ponens<
        add_hypothesis<premise, add_hypothesis<b, propositional::right_disjunction_introduction<c, d>>>,
        propositional::right_conjunction_elimination<implication<a, c>, implication<b, d>>
    >;
    using prop_premise_implies_a_or_b_implies_c_or_d = apply_conditional_modus_ponens_twice<
        add_hypothesis<premise, propositional::disjunction_elimination<a, b, disjunction<c, d>>>,
        prop_premise_implies_a_implies_c_or_d,
        prop_premise_implies_b_implies_c_or_d
    >;
    using result = prop_premise_implies_a_or_b_implies_c_or_d;
    static_assert(std::is_same_v<result, theorem<
        implication<conjunction<implication<a, c>, implication<b, d>>, implication<disjunction<a, b>, disjunction<c, d>>>
    >>);
};
template<typename a, typename b, typename c, typename d>
struct use_library_lemma_t<implication<conjunction<implication<a, c>, implication<b, d>>, implication<disjunction<a, b>, disjunction<c, d>>>> {
    using result = typename lemma__a_implies_c__and__b_implies_d__implies__a_or_b_implies_c_or_d<a, b, c, d>::result;
};

template<typename a, typename b, typename c, typename d>
struct lemma__a_implies_c__and__b_implies_d__implies__a_or_b_implies_d_or_c {  // ah!
    using premise = conjunction<implication<a, c>, implication<b, d>>;
    using prop_premise_implies_a_or_b_implies_c_or_d = use_library_lemma<
        implication<conjunction<implication<a, c>, implication<b, d>>, implication<disjunction<a, b>, disjunction<c, d>>>
    >;
    using prop_premise_implies_a_or_b_implies_d_or_c = apply_conditional_conditional_modus_ponens<
        add_hypothesis<premise, add_hypothesis<disjunction<a, b>, use_library_lemma<implication<disjunction<c, d>, disjunction<d, c>>>>>,
        prop_premise_implies_a_or_b_implies_c_or_d
    >;
    using result = prop_premise_implies_a_or_b_implies_d_or_c;
    static_assert(std::is_same_v<result, theorem<
        implication<conjunction<implication<a, c>, implication<b, d>>, implication<disjunction<a, b>, disjunction<d, c>>>
    >>);
};
template<typename a, typename b, typename c, typename d>
struct use_library_lemma_t<implication<conjunction<implication<a, c>, implication<b, d>>, implication<disjunction<a, b>, disjunction<d, c>>>> {
    using result = typename lemma__a_implies_c__and__b_implies_d__implies__a_or_b_implies_d_or_c<a, b, c, d>::result;
};


namespace lib_test {
    template<typename t>
    const bool library_proves = std::is_same_v<use_library_lemma<t>, theorem<t>>;
    struct a {};
    struct b {};
    struct c {};
    struct d {};

    static_assert(library_proves<multiary_implication<a, b, c, a>>);
    struct h1 {};
    struct h2 {};
    struct prop {};
    static_assert(library_proves<implication<ternary_implication<h1, h2, prop>, implication<conjunction<h1, h2>, prop>>>);
    static_assert(library_proves<implication<implication<conjunction<h1, h2>, prop>, ternary_implication<h1, h2, prop>>>);
    static_assert(library_proves<implication<ternary_implication<h1, h2, prop>, ternary_implication<h2, h1, prop>>>);
    static_assert(library_proves<implication<implication<conjunction<h1, h2>, prop>, implication<conjunction<h2, h1>, prop>>>);
    static_assert(library_proves<implication<implication<disjunction<h1, h2>, prop>, implication<disjunction<h2, h1>, prop>>>);

    static_assert(library_proves<implication<a, a>>);
    static_assert(library_proves<ternary_implication<implication<a, b>, implication<b, c>, implication<a, c>>>);
    static_assert(library_proves<implication<conjunction<implication<a, b>, implication<a, c>>, implication<a, conjunction<b, c>>>>);
    static_assert(library_proves<implication<conjunction<a, negation<a>>, False>>);
    static_assert(library_proves<implication<conjunction<implication<a, b>, implication<a, negation<b>>>, negation<a>>>);
    static_assert(library_proves<implication<a, negation<negation<a>>>>);
    static_assert(library_proves<implication<ternary_conjunction<a, b, c>, a>>);
    static_assert(library_proves<implication<ternary_conjunction<a, b, c>, b>>);
    static_assert(library_proves<implication<ternary_conjunction<a, b, c>, c>>);
    static_assert(library_proves<implication<implication<True, a>, a>>);
    static_assert(library_proves<implication<ternary_implication<a, b, c>, ternary_implication<a, negation<c>, negation<b>>>>);
    static_assert(library_proves<implication<conjunction<disjunction<a, b>, negation<a>>, b>>);
    static_assert(library_proves<implication<conjunction<disjunction<a, b>, negation<b>>, a>>);
    static_assert(library_proves<implication<negation<negation<a>>, a>>);  // classical
    static_assert(library_proves<implication<disjunction<a, b>, disjunction<b, a>>>);
    static_assert(library_proves<
        implication<conjunction<implication<a, c>, implication<b, d>>, implication<disjunction<a, b>, disjunction<c, d>>>
    >);
    static_assert(library_proves<
        implication<conjunction<implication<a, c>, implication<b, d>>, implication<disjunction<a, b>, disjunction<d, c>>>
    >);
}