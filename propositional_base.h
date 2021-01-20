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


template<typename, typename>
struct illformed_modus_ponens_application {};
template<typename Prop>
struct theorem {};
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

template<typename X, typename Y, typename Z>
using ternary_implication = implication<X, implication<Y, Z>>;

template<typename>
struct formulae::is_wff;
template<typename...>
struct formulae::are_wff;

namespace propositional {
    struct illformed_propositional_axiom_application {};

    template<typename a, typename b, typename c>
    using conditional_modus_ponens = typename std::conditional<are_wff<a, b, c>, theorem<
        ternary_implication<ternary_implication<a, b, c>, implication<a, b>, implication<a, c>>
    >, illformed_propositional_axiom_application>::type;
    template<typename a, typename b>
    using conjunction_introduction = typename std::conditional<are_wff<a, b>, theorem<
        ternary_implication<a, b, conjunction<a, b>>
    >, illformed_propositional_axiom_application>::type;
    template<typename a, typename b>
    using left_conjunction_elimination = typename std::conditional<are_wff<a, b>, theorem<
        implication<conjunction<a, b>, a>
    >, illformed_propositional_axiom_application>::type;
    template<typename a, typename b>
    using right_conjucntion_elimination = typename std::conditiona<are_wff<a, b>, theorem<
        implication<conjunction<a, b>, b>
    >, illformed_propositional_axiom_application>::type;
    template<typename a, typename b>
    using left_disjunction_introduction = typename std::conditional<are_wff<a, b>, theorem<
        implication<a, disjunction<a, b>>
    >, illformed_propositional_axiom_application>::type;
    template<typename a, typename b>
    using right_disjunction_introductin = typename std::conditional<are_wff<a, b>, theorem<
        implication<b, disjunction<a, b>>
    >, illformed_propositional_axiom_application>::type;
    template<typename a, typename b, typename c>
    using disjunction_elimination = typename std::conditional<are_wff<a, b, c>, theorem<
        ternary_implication<implication<a, c>, implication<b, c>, implication<disjunction<a, b>, c>>
    >, illformed_propositional_axiom_application>::type;
    template<typename a>
    using false_implies_anything = typename std::conditional<is_wff<a>::value, theorem<
        implication<False, a>
    >, illformed_propositional_axiom_application>::type;
    template<typename a>
    using law_of_excluded_middle = std::enable_if<allow_law_of_excluded_middle, std::conditional<is_wff<a>::value, theorem<
        disjunction<a, negation<a>>
    >, illformed_propositional_axiom_application>::type>::type;
}


#endif
