#ifndef _included_propositional_base
#define _included_propositional_base
#include <type_traits>


template<typename, typename>
struct implication {};
template<typename, typename>
struct conjunction {};
template<typename, typename>
struct disjunction {};
struct False {};
template<typename t>
using negation = implication<t, False>;  // warning: alias, not struct
// for convenience of making propositional proofs: no need to translate negation<t> into something
using True = negation<False>;
template<typename a, typename b>
using equivalence = conjunction<implication<a, b>, implication<b, a>>;

template<typename X, typename Y, typename Z>
using ternary_implication = implication<X, implication<Y, Z>>;


template<typename Prop>
struct theorem {};

template<typename, typename>
struct illformed_modus_ponens_application {};
template<typename th_A_implies_B, typename th_A>
struct modus_ponens {
    using result = illformed_modus_ponens_application<th_A_implies_B, th_A>;
};
template<typename A, typename B>
struct modus_ponens<theorem<implication<A, B>>, theorem<A>> {
    using result = theorem<B>;
};
template<typename th_A_implies_B, typename th_A>
using apply_modus_ponens = typename modus_ponens<th_A_implies_B, th_A>::result;
template<typename th_A_implies_B, typename th_A>
using apply_mp = apply_modus_ponens<th_A_implies_B, th_A>;


namespace formulae {
    template<typename>
    struct is_wff;
    template<typename...>
    struct are_wff;
}

namespace propositional {
    struct illformed_propositional_axiom_application {};

    const bool allow_law_of_excluded_middle = true;

    /*template<typename a, typename b>
    using hypothesis_addition = typename std::conditional<formulae::are_wff<a, b>::value, theorem<
        ternary_implication<a, b, a>
    >, illformed_propositional_axiom_application>::type;
    template<typename a, typename b, typename c>
    using conditional_modus_ponens = typename std::conditional<formulae::are_wff<a, b, c>::value, theorem<
        ternary_implication<ternary_implication<a, b, c>, implication<a, b>, implication<a, c>>
    >, illformed_propositional_axiom_application>::type;
    template<typename a, typename b>
    using conjunction_introduction = typename std::conditional<formulae::are_wff<a, b>::value, theorem<
        ternary_implication<a, b, conjunction<a, b>>
    >, illformed_propositional_axiom_application>::type;
    template<typename a, typename b>
    using left_conjunction_elimination = typename std::conditional<formulae::are_wff<a, b>::value, theorem<
        implication<conjunction<a, b>, a>
    >, illformed_propositional_axiom_application>::type;
    template<typename a, typename b>
    using right_conjunction_elimination = typename std::conditional<formulae::are_wff<a, b>::value, theorem<
        implication<conjunction<a, b>, b>
    >, illformed_propositional_axiom_application>::type;
    template<typename a, typename b>
    using left_disjunction_introduction = typename std::conditional<formulae::are_wff<a, b>::value, theorem<
        implication<a, disjunction<a, b>>
    >, illformed_propositional_axiom_application>::type;
    template<typename a, typename b>
    using right_disjunction_introductin = typename std::conditional<formulae::are_wff<a, b>::value, theorem<
        implication<b, disjunction<a, b>>
    >, illformed_propositional_axiom_application>::type;
    template<typename a, typename b, typename c>
    using disjunction_elimination = typename std::conditional<formulae::are_wff<a, b, c>::value, theorem<
        ternary_implication<implication<a, c>, implication<b, c>, implication<disjunction<a, b>, c>>
    >, illformed_propositional_axiom_application>::type;
    template<typename a>
    using false_implies_anything = typename std::conditional<formulae::is_wff<a>::value, theorem<
        implication<False, a>
    >, illformed_propositional_axiom_application>::type;
    template<typename a>
    using law_of_excluded_middle = typename std::enable_if<allow_law_of_excluded_middle,
        typename std::conditional<formulae::is_wff<a>::value, theorem<
            disjunction<a, negation<a>>
        >, illformed_propositional_axiom_application>::type
    >::type;*/

    template<typename a, typename b>
    using hypothesis_addition = theorem<ternary_implication<a, b, a>>;
    template<typename a, typename b, typename c>
    using conditional_modus_ponens = theorem<ternary_implication<ternary_implication<a, b, c>, implication<a, b>, implication<a, c>>>;
    template<typename a, typename b>
    using conjunction_introduction = theorem<ternary_implication<a, b, conjunction<a, b>>>;
    template<typename a, typename b>
    using left_conjunction_elimination = theorem<implication<conjunction<a, b>, a>>;
    template<typename a, typename b>
    using right_conjunction_elimination = theorem<implication<conjunction<a, b>, b>>;
    template<typename a, typename b>
    using left_disjunction_introduction = theorem<implication<a, disjunction<a, b>>>;
    template<typename a, typename b>
    using right_disjunction_introduction = theorem<implication<b, disjunction<a, b>>>;
    template<typename a, typename b, typename c>
    using disjunction_elimination = theorem<ternary_implication<implication<a, c>, implication<b, c>, implication<disjunction<a, b>, c>>>;
    template<typename a>
    using false_implies_anything = theorem<implication<False, a>>;
    template<typename a>
    using law_of_excluded_middle = std::enable_if_t<allow_law_of_excluded_middle, theorem<disjunction<a, negation<a>>>>;
}


#endif