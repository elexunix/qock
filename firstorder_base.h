#ifndef _included_firstorder_base
#define _included_firstorder_base
#include <tuple>
#include "propositional_base.h"


template<bool>
struct switch_type : std::true_type {};
template<>
struct switch_type<false> : std::false_type {};
struct _undefined_t {  // if this is returned, something went wrong; for implementation purposes only
    static const bool undefined = true;
};
template<typename...>
struct some_truetype : std::false_type {};
template<typename t, typename... others>
struct some_truetype<t, others...> : switch_type<t::value || some_truetype<others...>::value> {};
template<typename...>
struct all_truetypes : std::true_type {};
template<typename t, typename... others>
struct all_truetypes<t, others...> : switch_type<t::value && all_truetypes<others...>::value> {};


namespace terms {
    template<typename>
    struct variable {};
    template<typename>
    struct is_wellformed_term : std::false_type {};
    template<typename... terms>
    struct are_wellformed_terms : all_truetypes<is_wellformed_term<terms>...> {};

    template<template<typename...> typename, typename>
    struct is_term_container_composable_with_terminal : std::false_type {};
    template<template<typename...> typename, template<typename...> typename>
    struct are_term_containers_composable : std::false_type {};

    // only unary and binary outer containers are supported
    template<template<typename> typename outer_container, typename terminal>
    struct is_wellformed_term<outer_container<terminal>>
            : switch_type<is_term_container_composable_with_terminal<outer_container, terminal>::value && is_wellformed_term<terminal>::value>
            {};
    template<template<typename> typename outer_container, template<typename...> typename inner_container, typename... args>
    struct is_wellformed_term<outer_container<inner_container<args...>>>
            : switch_type<are_term_containers_composable<outer_container, inner_container>::value
                && is_wellformed_term<inner_container<args...>>::value>
            {};
    template<template<typename, typename> typename outer, typename terminal1, typename terminal2>
    struct is_wellformed_term<outer<terminal1, terminal2>>
            : switch_type<is_term_container_composable_with_terminal<outer, terminal1>::value && is_wellformed_term<terminal1>::value
                && is_term_container_composable_with_terminal<outer, terminal2>::value && is_wellformed_term<terminal2>::value>
            {};
    template<template<typename, typename> typename outer, typename terminal, template<typename...> typename inner, typename... args>
    struct is_wellformed_term<outer<terminal, inner<args...>>>
            : switch_type<is_term_container_composable_with_terminal<outer, terminal>::value && is_wellformed_term<terminal>::value
                && are_term_containers_composable<outer, inner>::value && is_wellformed_term<inner<args...>>::value>
            {};
    template<template<typename, typename> typename outer, template<typename...> typename inner, typename... args, typename terminal>
    struct is_wellformed_term<outer<inner<args...>, terminal>>
            : switch_type<is_term_container_composable_with_terminal<outer, terminal>::value && is_wellformed_term<terminal>::value
                && are_term_containers_composable<outer, inner>::value && is_wellformed_term<inner<args...>>::value>
            {};
    template<template<typename, typename> typename outer, template<typename...> typename inner1, typename... inner1_args,
            template<typename...> typename inner2, typename... inner2_args>
    struct is_wellformed_term<outer<inner1<inner1_args...>, inner2<inner2_args...>>>
            : switch_type<are_term_containers_composable<outer, inner1>::value && are_term_containers_composable<outer, inner2>::value
                && are_wellformed_terms<inner1<inner1_args...>, inner2<inner2_args...>>::value>
            {};

    template<typename a>
    using mb_variable = is_wellformed_term<variable<a>>;
    template<typename, typename>
    struct variable_occurs_in_term;
    template<typename a, typename b>
    struct variable_occurs_in_term<a, variable<b>> : std::is_same<a, b> {};
}


namespace atoms {
    using namespace terms;

    template<typename>
    struct is_wellformed_atom : std::false_type {};
    template<typename... atoms>
    struct are_wellformed_atoms : all_truetypes<is_wellformed_atom<atoms>...> {};

    template<template<typename...> typename, typename>
    struct is_atom_container_composable_with_terminal : std::false_type {};
    template<template<typename...> typename, template<typename...> typename>
    struct are_atom_term_containers_composable : std::false_type {};

    // only unary and binary containers are supported
    template<template<typename> typename atom_container, typename terminal>
    struct is_wellformed_atom<atom_container<terminal>>
            : switch_type<is_atom_container_composable_with_terminal<atom_container, terminal>::value && is_wellformed_term<terminal>::value>
            {};
    template<template<typename> typename atom_container, template<typename...> typename term_container, typename... term_args>
    struct is_wellformed_atom<atom_container<term_container<term_args...>>>
            : switch_type<are_atom_term_containers_composable<atom_container, term_container>::value
                && is_wellformed_term<term_container<term_args...>>::value>
            {};
    template<template<typename, typename> typename atom_container, typename terminal,
            template<typename...> typename term_container, typename... term_args>
    struct is_wellformed_atom<atom_container<terminal, term_container<term_args...>>>
            : switch_type<is_atom_container_composable_with_terminal<atom_container, terminal>::value && is_wellformed_term<terminal>::value
                && are_atom_term_containers_composable<atom_container, term_container>::value
                && is_wellformed_term<term_container<term_args...>>::value>
            {};
    template<template<typename, typename> typename atom_container, template<typename...> typename term_container, typename... term_args,
            typename terminal>
    struct is_wellformed_atom<atom_container<term_container<term_args...>, terminal>>
            : switch_type<is_atom_container_composable_with_terminal<atom_container, terminal>::value && is_wellformed_term<terminal>::value
                && are_atom_term_containers_composable<atom_container, term_container>::value
                && is_wellformed_term<term_container<term_args...>>::value>
            {};
    template<template<typename, typename> typename atom_container, template<typename...> typename term_container_1, typename... args1,
            template<typename...> typename term_container_2, typename... args2>
    struct is_wellformed_atom<atom_container<term_container_1<args1...>, term_container_2<args2...>>>
            : switch_type<are_atom_term_containers_composable<atom_container, term_container_1>::value
                && are_atom_term_containers_composable<atom_container, term_container_2>::value
                && is_wellformed_term<term_container_1<args1...>>::value && is_wellformed_term<term_container_2<args2...>>::value>
            {};

    template<typename a, typename b>
    struct variable_occurs_in_atom : _undefined_t {};
}


template<typename, typename>
struct forall {};
template<typename x, typename phi>
using exists = negation<forall<x, negation<phi>>>;

namespace formulae {
    using namespace atoms;

    template<typename alpha, typename phi>
    struct variable_occurs_in_formula : variable_occurs_in_atom<alpha, phi> {};
    template<typename alpha, typename phi, typename psi>
    struct variable_occurs_in_formula<alpha, implication<phi, psi>>
            : switch_type<variable_occurs_in_formula<alpha, phi>::value || variable_occurs_in_formula<alpha, psi>::value>
            {};
    template<typename alpha, typename phi, typename psi>
    struct variable_occurs_in_formula<alpha, conjunction<phi, psi>>
            : switch_type<variable_occurs_in_formula<alpha, phi>::value || variable_occurs_in_formula<alpha, psi>::value>
            {};
    template<typename alpha, typename phi, typename psi>
    struct variable_occurs_in_formula<alpha, disjunction<phi, psi>>
            : switch_type<variable_occurs_in_formula<alpha, phi>::value || variable_occurs_in_formula<alpha, psi>::value>
            {};
    template<typename alpha, typename x, typename phi>
    struct variable_occurs_in_formula<alpha, forall<x, phi>>
            : switch_type<std::is_same<alpha, x>::value || variable_occurs_in_formula<alpha, phi>::value>
            {};
    template<typename alpha, typename... phis>
    struct variable_occurs_in_some_formula : some_truetype<variable_occurs_in_formula<alpha, phis>...> {};

    template<typename, typename>
    struct variable_is_quantified_over_in_formula : std::false_type {};  // variables are not quantified over in atoms
    template<typename var, typename phi, typename psi>
    struct variable_is_quantified_over_in_formula<var, implication<phi, psi>>
            : switch_type<variable_is_quantified_over_in_formula<var, phi>::value || variable_is_quantified_over_in_formula<var, psi>::value>
            {};
    template<typename var, typename phi, typename psi>
    struct variable_is_quantified_over_in_formula<var, conjunction<phi, psi>>
            : switch_type<variable_is_quantified_over_in_formula<var, phi>::value || variable_is_quantified_over_in_formula<var, psi>::value>
            {};
    template<typename var, typename phi, typename psi>
    struct variable_is_quantified_over_in_formula<var, disjunction<phi, psi>>
            : switch_type<variable_is_quantified_over_in_formula<var, phi>::value || variable_is_quantified_over_in_formula<var, psi>::value>
            {};
    template<typename var, typename x, typename phi>
    struct variable_is_quantified_over_in_formula<var, forall<x, phi>>
            : switch_type<std::is_same<var, x>::value || variable_is_quantified_over_in_formula<var, phi>::value>
            {};

    template<typename t>
    struct is_wff : is_wellformed_atom<t> {};
    template<typename phi>
    using is_wellformed_formula = is_wff<phi>;
    template<typename phi, typename psi>
    struct is_wff<implication<phi, psi>> : switch_type<is_wff<phi>::value && is_wff<psi>::value> {};
    template<typename phi, typename psi>
    struct is_wff<conjunction<phi, psi>> : switch_type<is_wff<phi>::value && is_wff<psi>::value> {};
    template<typename phi, typename psi>
    struct is_wff<disjunction<phi, psi>> : switch_type<is_wff<phi>::value && is_wff<psi>::value> {};
    template<>
    struct is_wff<False> : std::true_type {};
    template<typename x, typename phi>
    struct is_wff<forall<x, phi>>
            : switch_type<mb_variable<x>::value && !variable_is_quantified_over_in_formula<x, phi>::value && is_wff<phi>::value>
            {};
    template<typename... phis>
    struct are_wff : all_truetypes<is_wff<phis>...> {};

    template<typename alpha, typename beta, typename phi>
    struct replace_free_variable_with_term : _undefined_t {};  // replaces all variable<alpha> with beta,
                                                            // e.g., sum<variable<alpha>, Zero> -> sum<beta, Zero>
    template<typename alpha, typename beta, typename gamma>
    struct replace_free_variable_with_term<alpha, beta, variable<gamma>> {
        using result = typename std::conditional<std::is_same<alpha, gamma>::value, beta, variable<gamma>>::type;
    };
    template<typename alpha, typename beta, typename phi, typename psi>
    struct replace_free_variable_with_term<alpha, beta, implication<phi, psi>> {
        using result = implication<typename replace_free_variable_with_term<alpha, beta, phi>::result,
            typename replace_free_variable_with_term<alpha, beta, psi>::result>;
    };
    template<typename alpha, typename beta, typename phi, typename psi>
    struct replace_free_variable_with_term<alpha, beta, conjunction<phi, psi>> {
        using result = conjunction<typename replace_free_variable_with_term<alpha, beta, phi>::result,
            typename replace_free_variable_with_term<alpha, beta, psi>::result>;
    };
    template<typename alpha, typename beta, typename phi, typename psi>
    struct replace_free_variable_with_term<alpha, beta, disjunction<phi, psi>> {
        using result = disjunction<typename replace_free_variable_with_term<alpha, beta, phi>::result,
            typename replace_free_variable_with_term<alpha, beta, psi>::result>;
    };
    template<typename alpha, typename beta>
    struct replace_free_variable_with_term<alpha, beta, False> {
        using result = False;
    };
    template<typename alpha, typename beta, typename gamma, typename phi>
    struct replace_free_variable_with_term<alpha, beta, forall<gamma, phi>> {
        using result = forall<gamma, typename replace_free_variable_with_term<alpha, beta, phi>::result>;
    };

    template<typename, typename>
    struct some_term_variable_occurs_in_formula;  // formula is assumed to be well-formed
    template<typename a, typename phi>
    struct some_term_variable_occurs_in_formula<variable<a>, phi> : variable_occurs_in_formula<a, phi> {};
    template<typename, typename>
    struct some_term_variable_is_quantified_over_in_formula;  // --//--
    template<typename a, typename phi>
    struct some_term_variable_is_quantified_over_in_formula<variable<a>, phi> : variable_is_quantified_over_in_formula<a, phi> {};

    template<typename a, typename phi>
    struct variable_occurs_free_in_formula  // issued
            : switch_type<variable_occurs_in_formula<a, phi>::value && !variable_is_quantified_over_in_formula<a, phi>::value>
            {};
}


template<typename alpha, typename conditioned_premise_, typename conditioned_conclusion_, typename...>
struct illformed_universal_introduction {
    using a = alpha;
    using conditioned_premise = conditioned_premise_;
    using conditioned_conclusion = conditioned_conclusion_;
};

template<typename alpha, typename th_conditioned_premise, typename conditioned_conclusion>
struct universal_introduction : illformed_universal_introduction<alpha, th_conditioned_premise, conditioned_conclusion> {};
template<typename alpha, typename hypothesis, typename phi>
struct universal_introduction<alpha, theorem<implication<hypothesis, phi>>, implication<hypothesis, forall<alpha, phi>>> {
    using th_conditioned_premise = implication<hypothesis, phi>;
    using conditioned_conclusion = implication<hypothesis, forall<alpha, phi>>;
    using result = typename std::conditional<terms::mb_variable<alpha>::value && formulae::is_wff<th_conditioned_premise>::value
        && formulae::is_wff<conditioned_conclusion>::value && !formulae::variable_occurs_free_in_formula<alpha, hypothesis>::value, /* ! */
        theorem<conditioned_conclusion>, illformed_universal_introduction<alpha, th_conditioned_premise, conditioned_conclusion>
    >::type;
};

template<typename alpha, typename th_conditioned_premise, typename conditioned_conclusion>
using apply_universal_introduction = typename universal_introduction<alpha, th_conditioned_premise, conditioned_conclusion>::result;
template<typename alpha, typename th_conditioned_premise, typename conditioned_conclusion>
using universal_generalization = universal_introduction<alpha, th_conditioned_premise, conditioned_conclusion>;
template<typename alpha, typename th_conditioned_premise, typename conditioned_conclusion>
using apply_universal_generalization = apply_universal_introduction<alpha, th_conditioned_premise, conditioned_conclusion>;

struct illformed_axiom {};

namespace firstorder {
    template<typename alpha, typename beta, typename antecedent_, typename consequent_, typename...>
    struct illformed_universal_elimination : illformed_axiom {
        using a = alpha;
        using b = beta;
        using antecedent = antecedent_;
        using consequent = consequent_;
    };
    template<typename alpha, typename beta, typename antecedent, typename consequent>
    struct universal_elimination : illformed_universal_elimination<alpha, beta, antecedent, consequent> {};
    template<typename alpha, typename beta, typename phi, typename phi_prime>
    struct universal_elimination<alpha, beta, forall<alpha, phi>, phi_prime> {
        using result = typename std::conditional<terms::mb_variable<alpha>::value && terms::is_wellformed_term<beta>::value
            //&& !terms::variable_occurs_in_term<alpha, beta>::value
            && !formulae::some_term_variable_is_quantified_over_in_formula<beta, phi_prime>::value
            && std::is_same<phi_prime, typename formulae::replace_free_variable_with_term<alpha, beta, phi>::result>::value,
            theorem<implication<forall<alpha, phi>, phi_prime>>, illformed_universal_elimination<alpha, beta, forall<alpha, phi>, phi_prime>
        >::type;
    };

    template<typename alpha, typename beta, typename antecedent, typename consequent>
    using apply_universal_elimination = typename universal_elimination<alpha, beta, antecedent, consequent>::result;
    template<typename alpha, typename beta, typename antecedent, typename consequent>
    using universal_instantiation = universal_elimination<alpha, beta, antecedent, consequent>;
    template<typename alpha, typename beta, typename antecedent, typename consequent>
    using apply_universal_instantiation = apply_universal_elimination<alpha, beta, antecedent, consequent>;
}


namespace axioms {
    using namespace formulae;
}


#endif