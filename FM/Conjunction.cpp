// Created on: Jun 20, 2015
// Author: Diogo N. SAMPAIO <dnsampaio@gmail.com>
//
//===-- /Simplifier/Conjunction.cpp - {Description} -------*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
///
/// \file
/// \brief
///
//===----------------------------------------------------------------------===//

#include "Conjunction.hpp"
#include "Simplifier.hpp"
#include <cmath>
#include <regex>

#include "debug.hpp"

using namespace std;
using namespace GiNaC;

Conjunction Conjunction::obvious = Make(true);
Conjunction Conjunction::absurd = Make(false);
unsigned Conjunction::counter = 0;

Conjunction::Conjunction() : tester(nullptr), _id(counter++) {}

Conjunction Conjunction::Make(bool val) {
  Conjunction c;
  if (not val)
    c.eqs.insert(&Constraint::falseC);

  return c;
}

Conjunction::Conjunction(const Symbols &v, const Symbols &p,
                         const Constraints &e, const Constraints &i,
                         const unsigned id)
    : vars(v), pars(p), eqs(e), ineqs(i), tester(nullptr), _id(id) {
  ineqs.erase(Constraint::getTrue());
  eqs.erase(Constraint::getTrue());
  if (eqs.find(Constraint::getFalse()) != eqs.end() or
      ineqs.find(Constraint::getFalse()) != ineqs.end()) {
    *this = absurd;
    return;
  } else if (eqs.empty() and ineqs.empty()) {
    *this = obvious;
    return;
  } else {
    removeUnused();
  }

  for (cc c : ineqs) {
    if (ineqs.find(c->getNot()) != ineqs.end()) {
      DEBUG(1, "This system contains to inverse constraints:"
                   << c << " AND " << c->getNot() << NL);
      makeFalse();
      return;
    }
  }
  for (cc c : ineqs) {
    if (ineqs.find(c->getNot()) != ineqs.end()) {
      DEBUG(1, "This system contains to inverse constraints:"
                   << c << " AND " << c->getNot() << NL);
      makeFalse();
      return;
    }
  }

  for (auto it1 = ineqs.begin(); it1 != ineqs.end(); it1++) {
    cc c = *it1;
    if (ineqs.find(c->getNot()) != ineqs.end()) {
      DEBUG(1, "This system contains to inverse constraints:"
                   << c << " AND " << c->getNot() << NL);
      makeFalse();
      return;
    }
  }
}

Conjunction::Conjunction(const Symbols &v, const Symbols &p,
                         const Constraints &constr, const unsigned id)
    : vars(v), pars(p), tester(nullptr), _id(id) {
  for (cc c : constr)
    if (c->eq)
      eqs.insert(c);
    else
      ineqs.insert(c);
}

Conjunction::Conjunction(string &in) : tester(nullptr), _id(counter++) {
  DEBUG(10, "Starting string: " << in << NL << NL);
  size_t s = in.find(':');
  if (s == string::npos) {
    cerr << "Can't find conjunction start delimiter \":\"\n";
    exit(BAD_INPUT);
  }
  regex rg("\\[[-0-9]+\\]");
  regex ge(u8"≥");
  regex le(u8"≤");

  string constraintsStr = regex_replace(
      regex_replace(regex_replace(in.substr(s + 1), ge, ">="), le, "<="), rg,
      "");
  string tst = constraintsStr;
  for (auto &c : tst)
    c = toupper(c);
  if (tst == "FALSE") {
    makeFalse();
    return;
  }

  if (tst == "TRUE") {
    *this = Conjunction::obvious;
    return;
  }

  DEBUG(10, "Constraints:" << constraintsStr << NL << NL);
  in = in.substr(0, s - 1);
  DEBUG(10, "Pars/vars string:" << in << NL << NL);
  s = in.find("]->[");
  string parsStr = "";
  if (s != string::npos) {
    parsStr = in.substr(1, s - 1);
    in = in.substr(s + 4);
  }
  DEBUG(10, "Parameters:" << parsStr << NL);
  DEBUG(10, "Variables:" << in << NL);

  if (in.empty() and parsStr.empty()) {
    cerr << "No variables and no parameters to the conjunction\n";
    exit(BAD_INPUT);
  }

  variablesStr2set(in, vars);
  DEBUG(10, "System variables: " << vars << NL);
  variablesStr2set(parsStr, pars);
  DEBUG(10, "System parameters: " << pars << NL);

  for (s = constraintsStr.find_first_of('&'); s != string::npos;
       s = constraintsStr.find_first_of('&')) {
    string newConstraintStr = constraintsStr.substr(0, s);
    constraintsStr = constraintsStr.substr(s + 1);
    DEBUG(10,
          "Obtaining constraint from the string: " << newConstraintStr << NL);
    cc c = Constraint::get(newConstraintStr);
    DEBUG(10, "Generated constraint: " << c << NL);
    if (c == Constraint::getFalse()) {
      DEBUG(1, "FALSE\n");
      makeFalse();
      return;
    }
    if (c == Constraint::getTrue())
      continue;

    if (c->eq)
      eqs.insert(c);
    else {
      if (ineqs.find(c->getNot()) != ineqs.end()) {
        cerr << "Holding " << c << " and " << c->getNot()
             << " makes the system empty.\n";
        makeFalse();
        return;
      }
      ineqs.insert(c);
    }
  }
  {
    cc c = Constraint::get(constraintsStr);
    if (c == Constraint::getFalse()) {
      DEBUG(1, "FALSE\n");
      makeFalse();
      return;
    }
    if (c != Constraint::getTrue()) {
      if (c->eq)
        eqs.insert(c);
      else {
        if (ineqs.find(c->getNot()) != ineqs.end()) {
          cerr << "Holding " << c << " and " << c->getNot()
               << " makes the system empty.\n";
          makeFalse();
          return;
        }
        ineqs.insert(c);
      }
    }
  }

  //  buildTester();
  detectEqs();
  if (empty()) {
    *this = obvious;
    return;
  }

  DEBUG(4, "Input system is:\n" << *this << NL);
  removeUnused();
}

ostream &Conjunction::print(ostream &out) const {
  string nl = "\n";
  string tab = "\t";
  string start = "\n";
  static std::streambuf const *cerrbuf = std::cerr.rdbuf();
  if (out.rdbuf() != cerrbuf) {
    nl = " ";
    tab = " ";
    start = "";
  }
  out << '[';
  string before = "";
  for (const ex &s : pars) {
    out << before << s;
    before = ",";
  }
  out << "]->[";
  before = "";
  for (const ex &s : vars) {
    out << before << s;
    before = ",";
  }
  out << "]:";

  if (absurd == *this)
    out << "false";
  else if (obvious == *this)
    out << "true";
  else {
    out << start;
    string bef = tab;
    for (cc c : eqs) {
      out << bef << c;
      bef = " &" + nl;
      if (nl != tab)
        bef += tab;
    }
    for (cc c : ineqs) {
      out << bef << c;
      bef = " &" + nl;
      if (nl != tab)
        bef += tab;
    }
  }
  out << ";";
  return out;
}

ostream &Conjunction::c_print(ostream &out) const {
  if ((size() == 0) or (Conjunction::obvious == *this))
    return (out << "(1)");

  if (*this == Conjunction::absurd)
    return (out << "(0)");

  string before = "(";
  for (cc c : eqs) {
    out << before;
    c->c_print(out);
    before = ")&&(";
  }
  for (cc c : ineqs) {
    out << before;
    c->c_print(out);
    before = ")&&(";
  }
  out << ')';
  return out;
}

void Conjunction::insert(const string &constraint) {
  if (constraint.empty())
    return;
  cc c = Constraint::get(constraint);
  if (c->eq) {
    if (c == Constraint::getFalse()) {
      DEBUG(1, "FALSE\n");
      makeFalse();
    }
    if (c != Constraint::getTrue())
      eqs.insert(c);
  } else {
    if (ineqs.find(c->getNot()) != ineqs.end()) {
      DEBUG(1, "This system contains to inverse constraints:"
                   << c << " AND " << c->getNot() << NL);
      makeFalse();
    } else
      ineqs.insert(c);
  }
}

bool Conjunction::implies(const Conjunction &other) {
  Constraints oeqs = other.eqs;
  Constraints oineqs = other.ineqs;

  if (other == Conjunction::absurd) {
    return (*this == Conjunction::absurd);
  }

  if (other == Conjunction::obvious)
    return true;

  if (*this == Conjunction::absurd)
    return false;

  for (cc eq : eqs) {
    oeqs.erase(eq);
    oineqs.erase(Constraint::get(eq->exp));
    oineqs.erase(Constraint::get(-eq->exp));
  }

  for (cc eq : oeqs) {
    oineqs.insert(Constraint::get(eq->exp));
    oineqs.insert(Constraint::get(-eq->exp));
  }

  oeqs.clear();

  for (cc v : ineqs) {
    oineqs.erase(v);
  }

  if (oineqs.empty())
    return true;

  for (const ex &x : other.pars)
    if (not(pars.has(x) or vars.has(x)))
      return false;

  for (const ex &x : other.vars)
    if (not(pars.has(x) or vars.has(x)))
      return false;

  if ((not oineqs.empty()) && (tester == nullptr))
    getTester();

  while (not oineqs.empty()) {
    Constraints::iterator tt = oineqs.begin();
    auto res = tester->test((*tt)->exp);
    switch (res.sign) {
    case SIGN::GEZ:
    case SIGN::GTZ:
    case SIGN::ZERO:
      oineqs.erase(tt);
      continue;
    case SIGN::ABSURD: {
      DEBUG(1, "FALSE\n");
      makeFalse();
      return false;
    }
    default:
      return false;
    }
  }
  return true;
}

void Conjunction::removeUnused() {
  removeUnused(pars);
  removeUnused(vars);
}

void Conjunction::removeUnused(Symbols &toSimplify) {
  toSimplify.sort();
  toSimplify.unique();
  Symbols remaining;
  for (const ex &e : toSimplify) {
    bool found = false;
    for (cc c : eqs) {
      if (quo(c->exp, e, e) != 0) {
        remaining.append(e);
        found = true;
        break;
      }
    }
    if (found)
      continue;
    for (cc c : ineqs) {
      if (quo(c->exp, e, e) != 0) {
        remaining.append(e);
        found = true;
        break;
      }
    }
  }
  swap(toSimplify, remaining);
}

bool Conjunction::operator==(const Conjunction &other) const {
  return ((vars == other.vars) and (pars == other.pars) and
          (eqs == other.eqs) and (ineqs == other.ineqs));
}

bool Conjunction::hasVariables() const { return (vars.nops() != 0); }

Conjunction Conjunction::operator&(const Conjunction &other) const {
  Conjunction out(other);
  out.tester = nullptr;

  for (const ex &s : pars)
    out.pars.append(s);

  for (const ex &s : vars)
    out.vars.append(s);

  out.removeJoin({}, eqs);
  out.removeJoin({}, ineqs);

  out.removeUnused();
  return out;
}

Conjunction Conjunction::operator&(const cc c) const {
  if (c == Constraint::getFalse())
    return absurd;

  if (c == Constraint::getTrue())
    return *this;

  Conjunction out(*this);
  out.tester = nullptr;

  if (c->eq)
    out.eqs.insert(c);
  else
    out.ineqs.insert(c);

  return out;
}

Conjunction Conjunction::operator&(const Constraints &clauses) const {
  Conjunction out(*this);
  out.tester = nullptr;
  for (const cc c : clauses) {
    if (c == Constraint::getFalse())
      return absurd;

    if (c == Constraint::getTrue())
      continue;

    if (c->eq)
      out.eqs.insert(c);
    else
      out.ineqs.insert(c);
  }

  return out;
}

bool Conjunction::removeJoin(const Constraints &toRemove,
                             const Constraints &toJoin) {
  if (*this == absurd)
    return false;

  bool changed = false;
  for (const cc c : toRemove) {
    if (c->eq)
      changed |= (eqs.erase(c) != 0);

    else
      changed |= (ineqs.erase(c) != 0);
  }
  for (const cc c : toJoin) {
    if (c == Constraint::getFalse()) {
      DEBUG(4, "Got an false constraint to join, returning absurd system\n");
      *this = absurd;
      return true;
    }

    if (c == Constraint::getTrue()) {
      DEBUG(4, "Ignoring the insert of a true constraint\n");
      continue;
    }
    if (c->eq)
      changed |= eqs.insert(c).second;

    else
      changed |= ineqs.insert(c).second;
  }
  if (empty())
    *this = obvious;

  removeUnused();
  if (changed) {
    clearTester();
    return true;
  }
  return false;
}

bool Conjunction::hasInverseConstraints() const {
  if (*this == absurd)
    return true;

  if (*this == obvious)
    return false;

  for (cc c : ineqs)
    if ((c->id < 0) and (ineqs.find(c->getNot()) != ineqs.end()))
      return true;
  return false;
}

bool Conjunction::empty() const { return (eqs.empty() and ineqs.empty()); }

bool Conjunction::hasEqs() const {
  if ((*this == absurd) or (*this == obvious))
    return false;
  return (eqs.size() > 0);
}

void Conjunction::makeFalse() {
  clearTester();
  *this = Conjunction::absurd;
}

void Conjunction::variablesStr2set(string &str, Symbols &s) {
  if (str.empty())
    return;

  for (size_t p = str.find_first_of(','); p != string::npos;
       p = str.find_first_of(',')) {
    string var = str.substr(0, p);
    str = str.substr(p + 1);
    if (var.length() == 0)
      continue;

    Constraint::cs symb = Constraint::getOrInsertSymbol(var);
    if (not(is_a<symbol>(symb))) {
      cerr << "Can't get symbol '" << var << "'\n";
      exit(BAD_INPUT);
    }
    s.append(symb);
  }

  if (str.length() == 0)
    return;

  Constraint::cs symb = Constraint::getOrInsertSymbol(str);
  if (not(is_a<symbol>(symb))) {
    cerr << "Can't get symbol '" << str << "'\n";
    exit(BAD_INPUT);
  }
  s.append(symb);
}

ostream &operator<<(ostream &out, const Conjunction &c) { return c.print(out); }
