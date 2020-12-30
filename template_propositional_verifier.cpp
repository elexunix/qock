#include <type_traits>

template<typename X, typename Y>
struct implication {};
template<typename X, typename Y>
struct conjunction {};
template<typename X, typename Y>
struct disjunction {};
struct False;
template<typename X>
struct negation : implication<X, False> {};
struct True : negation<False> {};

template<typename X, typename Y, typename Z>
struct illformed_modus_ponens_application {};
template<typename Prop>
struct is_wellformed_modus_ponens_application : std::true_type {};
template<typename X, typename Y, typename Z>
struct is_wellformed_modus_ponens_application<illformed_modus_ponens_application<X, Y, Z>> : std::false_type {};
template<typename Prop>
struct is_illformed_modus_ponens_application : std::false_type {};
template<typename X, typename Y, typename Z>
struct is_illformed_modus_ponens_application<illformed_modus_ponens_application<X, Y, Z>> : std::true_type {};
struct unproved_theorem {
    const bool proved = false;
};
struct proved_theorem {
    const bool proved = true;
};
template<typename Prop>
struct theorem : unproved_theorem {};
template<typename A_implies_B, typename A, typename B>
struct modus_ponens {
    using result = illformed_modus_ponens_application<A_implies_B, A, B>;
};
template<typename A, typename B>
struct modus_ponens<theorem<implication<A, B>>, theorem<A>, B> {
    using result = theorem<B>;
};
template<typename A, typename B, typename C>
using apply_modus_ponens = modus_ponens<A, B, C>::result;

template<typename A, typename B, typename C>
using ternary_implication = implication<A, implication<B, C>>;

const bool allow_law_of_excluded_middle = false;
template<typename a, typename b>
using axiom_hypothesis_addition = theorem<ternary_implication<a, b, a>>;
template<typename a, typename b, typename c>
using axiom_conditional_modus_ponens = theorem<ternary_implication<implication<a, b>, ternary_implication<a, b, c>, implication<a, c>>>;
template<typename a, typename b>
using axiom_conjunction_introduction = theorem<ternary_implication<a, b, conjunction<a, b>>>;
template<typename a, typename b>
using axiom_left_conjunction_elimination = theorem<implication<conjunction<a, b>, a>>;
template<typename a, typename b>
using axiom_right_conjunction_elimination = theorem<implication<conjunction<a, b>, b>>;
template<typename a, typename b>
using axiom_left_disjunction_introduction = theorem<implication<a, disjunction<a, b>>>;
template<typename a, typename b>
using axiom_right_disjunction_introduction = theorem<implication<b, disjunction<a, b>>>;
template<typename a, typename b, typename c>
using axiom_disjunction_elimination = theorem<ternary_implication<implication<a, b>, ternary_implication<a, b, c>, implication<a, c>>>;
template<typename a>
using axiom_law_of_excluded_middle = std::enable_if<allow_law_of_excluded_middle, theorem<disjunction<a, negation<a>>>>;

template<typename a>
struct theorem_a_implies_a {
    using b = implication<a, a>;
    using prop0 = axiom_conditional_modus_ponens<a, b, a>;
    using prop1 = apply_modus_ponens<prop0, axiom_hypothesis_addition<a, a>, implication<ternary_implication<a, b, a>, implication<a, a>>>;
    using prop2 = apply_modus_ponens<prop1, axiom_hypothesis_addition<a, b>, implication<a, a>>;
    using result = prop2;
};

int main() {
    struct a {};
    using proof = theorem_a_implies_a<a>;
    static_assert(is_wellformed_modus_ponens_application<proof::result>::value);
}