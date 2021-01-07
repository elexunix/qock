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

/*template<typename, typename, typename, typename>
struct illformed_ternary_modus_ponens_application {};
template<typename th_A_implies_B_implies_C, typename th_A, typename th_B, typename C>
struct ternary_modus_ponens {
    using result = illformed_ternary_modus_ponens_application<th_A_implies_B_implies_C, th_A, th_B, C>;
};
template<typename A, typename B, typename C>
struct ternary_modus_ponens<theorem<ternary_implication<A, B, C>>, theorem<A>, theorem<B>, C> {
    using result = theorem<C>;
};*/


namespace propositional {
    const bool allow_law_of_excluded_middle = true;
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
    using law_of_excluded_middle = std::enable_if<allow_law_of_excluded_middle, theorem<disjunction<a, negation<a>>>>;
}


#endif