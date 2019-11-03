// Created on: Oct 11, 2015
// Author: Diogo N. SAMPAIO <dnsampaio@gmail.com>
//
//===-- /Simplifier/Motzkin.cpp - {Description} -------*- C++ -*-===//
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
#include "Simplifier.hpp"
#include <array>
#include <cmath>
#include <ginac/ginac.h>

#include "debug.hpp"

#ifdef SCRIPT_CONTROL
#define returnAbsurd()                                                         \
  ;                                                                            \
  {                                                                            \
    cerr << __FILENAME__ << "::" << __func__ << "::" << __LINE__ << NL;        \
    tester->printResult(cerr);                                                 \
    cout.flush();                                                              \
    cerr.flush();                                                              \
    cout << Conjunction::absurd << NL;                                         \
    clear();                                                                   \
    exit(0);                                                                   \
  }
#else
#define returnAbsurd()                                                         \
  ;                                                                            \
  {                                                                            \
    messageM("Made the system false here");                                    \
    conju = Conjunction::absurd;                                               \
    ret.push_back(Conjunction::absurd);                                        \
  }                                                                            \
  while (0)
#endif

#define returnObvious()                                                        \
  {                                                                            \
    cout << Conjunction::obvious << NL;                                        \
    exit(0);                                                                   \
  }
#define sanityCheck()                                                          \
  {                                                                            \
    if ((Conjunction::absurd == conju) || conju.hasInverseConstraints()) {     \
      returnAbsurd();                                                          \
      return;                                                                  \
    } else if (Conjunction::obvious == conju) {                                \
      returnObvious();                                                         \
      return;                                                                  \
    }                                                                          \
  }

void Simplifier::build_tester() {
  clear();
  exset sys;
  if (Conjunction::absurd == conju)
    sys.insert(-1);
  else if (!(Conjunction::obvious == conju)) {
    for (cc c : conju.ineqs)
      sys.insert(c->exp);
    for (cc c : conju.eqs) {
      sys.insert(c->exp);
      sys.insert(-c->exp);
    }
  }
  DEBUGIF(6, "Tester received this set of constraints:\n") {
    int i = 1;
    for (const ex &e : sys)
      cerr << i++ << "  " << e << NL;
  }
  tester = new SchweighoferTester(sys);
}

void Simplifier::split_space(const exset &pars) {
  // If there are unknown or non strict relationship between 2 of these
  // expressions, split space
  for (exset::const_iterator pEnd = pars.end(), p1 = pars.begin(); p1 != pEnd;
       p1++) {
    for (exset::const_iterator p2 = next(p1); p2 != pEnd; p2++) {
      ex tt = (*p1) - (*p2);
      testResult tr = tester->test(tt);
      DEBUG(2, "Sign of " << tt << ":" << tr << NL);
      if (tr.sign == SIGN::ABSURD) {
        returnAbsurd();
        return;
      }
      switch (tr.sign) {
      case SIGN::LTZ:
      case SIGN::GTZ:
      case SIGN::ZERO:
        break;
      case SIGN::LEZ: {
        Conjunction cltz = conju;
        cltz.removeJoin({}, {Constraint::get(-tt - 1)});
        conju.removeJoin({}, {Constraint::get(-tt, true)});
#ifdef SCRIPT_CONTROL
        cout << conju << NL << cltz << NL;
        clear();
        exit(0);
#else
        ret.push_back(cltz);
        build_tester();
        return;
#endif
      }
      case SIGN::GEZ: {
        Conjunction cgtz = conju;
        cgtz.removeJoin({}, {Constraint::get(tt - 1)});
        conju.removeJoin({}, {Constraint::get(tt, true)});
#ifdef SCRIPT_CONTROL
        cout << conju << NL << cgtz << NL;
        clear();
        exit(0);
#else
        ret.push_back(cgtz);
        build_tester();
        return;
#endif
      }
      case SIGN::UNKNOWN: {
        Conjunction cgtz = conju;
        Conjunction cltz = conju;
        cgtz.removeJoin({}, {Constraint::get(tt - 1)});
        cltz.removeJoin({}, {Constraint::get(-tt - 1)});
        conju.removeJoin({}, {Constraint::get(tt, true)});
#ifdef SCRIPT_CONTROL
        cout << cltz << NL << conju << NL << cgtz << NL;
        clear();
        exit(0);
#else
        ret.push_back(cgtz);
        ret.push_back(cltz);
        build_tester();
        return;
#endif
      }
      case SIGN::ABSURD: {
        returnAbsurd();
        return;
      } break;
      }
    }
  }
}

Simplifier::relat Simplifier::put_in_evidence(ex exp, const exset &vars) const {
  if (vars.size() == 1) {
    ex v = *vars.begin();
    ex lhs = quo(exp, v, v);
    ex rhs = -rem(exp, v, v);
    if (!(is_a<numeric>(lhs)))
      return {v, lhs, rhs};
    return {0, 0, 0};
  }
  DEBUG(2, "TODO!!!\n");
  /* Ok, we have more than 1 variables to put in evidence.
   * 1st try to take highest degree and factorize. If you get an multiplication:
   * f*g=h, test if at least 2 of (f,g,h) have known signs 2nd try to move
   * reminder from all variables to other side. Try to factorize one side. If
   * successful test signs just as 1st step. If not ok, try other side. If
   * failed, return {0,0,0}
   */
  return {0, 0, 0};
}

bool Simplifier::eqs_affinize() {
  // The 2 most common equalities are: 1) linearized arrays 2) Packed symmetric
  // arrays. what patterns do they follow?
  bool changed = false;

  for (cc eq : conju.eqs) {
    DEBUG(3, "Checking equality " << eq << NL);
    exset parMaxDegree;
    int maxDegree = 0;
    for (ex p : conju.pars) {
      int dg = degree(eq->exp, p);
      if (dg == 0) {
        DEBUG(6, p << " is not in " << eq << NL);
        continue;
      }
      DEBUG(5, p << " has degree " << dg << " in " << eq << NL);
      if (dg > maxDegree) {
        maxDegree = dg;
        parMaxDegree.clear();
      }
      if (dg == maxDegree)
        parMaxDegree.insert(p);
    }

    if (maxDegree <= 1) { // Packed? The size depends in the position it self
      bool switchToVars = false;
      for (ex p : conju.vars) {
        int dg = degree(eq->exp, p);
        if (dg == 0) {
          DEBUG(6, p << " is not in " << eq << NL);
          continue;
        }
        if (dg > maxDegree) {
          switchToVars = true;
          maxDegree = dg;
          parMaxDegree.clear();
        }
        if ((dg == maxDegree) && switchToVars)
          parMaxDegree.insert(p);
      }
    }

    relat factorized;
    if ((maxDegree > 1) && (parMaxDegree.size() > 1))
      split_space(parMaxDegree);

    if (conju == Conjunction::absurd)
      return true;

    factorized = put_in_evidence(eq->exp, parMaxDegree);

    if (factorized.evidence == 0) {
      DEBUG(4, "Ignoring " << eq << NL);
      continue;
    }

    DEBUG(4, '(' << factorized.evidence << ") * (" << factorized.quo
                 << ") = " << factorized.rhs << NL);

    SIGN sEVI = tester->test(factorized.evidence).sign;
    if (sEVI == SIGN::ABSURD) {
      returnAbsurd();
      return true;
    }

    SIGN sQUO = tester->test(factorized.quo).sign;
    if (sQUO == SIGN::ABSURD) {
      returnAbsurd();
      return true;
    }

    SIGN sRHS = tester->test(factorized.rhs).sign;
    if (sRHS == SIGN::ABSURD) {
      returnAbsurd();
      return true;
    }

    DEBUG(4, sEVI << " * " << sQUO << " = " << sRHS << NL);
    if (sEVI == SIGN::ZERO) {
      if (sRHS != SIGN::UNKNOWN && (0 == (sRHS & SIGN::ZERO))) {
        returnAbsurd();
        return true;
      }
      sRHS = SIGN::ZERO;
      changed |= conju.removeJoin({}, {Constraint::get(factorized.rhs, true)});
    }

    if (sQUO == SIGN::ZERO) {
      if (sRHS != SIGN::UNKNOWN && (0 == (sRHS & SIGN::ZERO))) {
        returnAbsurd();
        return true;
      }
      sRHS = SIGN::ZERO;
      changed |= conju.removeJoin({}, {Constraint::get(factorized.rhs, true)});
    }

    if (sRHS == SIGN::ZERO) { // RHS = 0 ==> QUO = 0 or evidence = 0
      changed |= conju.removeJoin({}, {Constraint::get(factorized.rhs, true)});
      if ((sQUO & SIGN::ZERO) == 0) {
        DEBUG(4, "RHS = 0; QUO " << NE << " 0 ==> evidence = 0\n");
        changed |=
            conju.removeJoin({}, {Constraint::get(factorized.evidence, true)});
      }
      if ((sQUO & SIGN::ZERO) == 0) {
        DEBUG(4, "RHS = 0; QUO " << NE << " 0 ==> evidence = 0\n");
        changed |=
            conju.removeJoin({}, {Constraint::get(factorized.evidence, true)});
      }

      if ((sQUO != SIGN::UNKNOWN) && (sEVI != SIGN::UNKNOWN)) {
        if (((sQUO | sEVI) & SIGN::ZERO) == 0) {
          DEBUG(3, "(EVI " << NE << 0 << ") * (QUO " << NE << 0 << ") = 0?!\n");
          returnAbsurd();
          return true;
        }
      }
      if (0 == (sQUO & SIGN::ZERO)) {
        DEBUG(4, "(EVI ==> 0 ) * (QUO " << NE << " 0) = 0\n");
        changed |=
            conju.removeJoin({}, {Constraint::get(factorized.evidence, true)});
      } else if (0 == (sEVI & SIGN::ZERO)) {
        DEBUG(4, "(QUO ==> 0 ) * (EVI " << NE << " 0) = 0\n");
        changed |=
            conju.removeJoin({}, {Constraint::get(factorized.quo, true)});
      }
    } else if (sRHS != SIGN::UNKNOWN) {
      if (0 == (sRHS & SIGN::ZERO)) { // We have RHS == GTZ or LTZ
        switch (sEVI) {
        case SIGN::ZERO: {
          DEBUG(4, "This constraint is an absurd!!\n");
          returnAbsurd();
          return true;
        }
          // no break;
        case SIGN::GEZ: {
          sEVI = SIGN::GTZ;
          changed |=
              conju.removeJoin({}, {Constraint::get(factorized.evidence - 1)});
          DEBUG(4, factorized.evidence << " (evidence) = GEZ ==> GTZ\n"
                                       << conju << NL);
          break;
        }
        case SIGN::LEZ: {
          sEVI = SIGN::LTZ;
          changed |=
              conju.removeJoin({}, {Constraint::get(-factorized.evidence - 1)});
          DEBUG(4, factorized.evidence << " (evidence) = LEZ ==> LTZ\n"
                                       << conju << NL);
          break;
        }
        default:
          break;
        }
        switch (sQUO) {
        case SIGN::ZERO: {
          DEBUG(4, "This constraint is an absurd!!\n");
          returnAbsurd();
          return true;
        }
          // no break;
        case SIGN::GEZ: {
          sQUO = SIGN::GTZ;
          conju.removeJoin({}, {Constraint::get(factorized.quo - 1)});
          DEBUG(4, factorized.quo << " (QUO) = GEZ ==> GTZ\n" << conju << NL);
          break;
        }
        case SIGN::LEZ: {
          sQUO = SIGN::LTZ;
          conju.removeJoin({}, {Constraint::get(-factorized.quo - 1)});
          DEBUG(4, factorized.quo << " (QUO) = LEZ ==> LTZ\n" << conju << NL);
          break;
        }
        default:
          break;
        }

        if (sRHS == SIGN::GTZ) {
          if (sEVI ==
              SIGN::UNKNOWN) { // (evidence = UNKNOWN) * (QUO) = (RHS > 0)
            switch (sQUO) {
            case SIGN::LTZ: { // (evidence = UNKNOWN) * (QUO < 0) = (RHS > 0)
              DEBUG(4, "evidence = UNKNOWN ==> LTZ; QUO = LTZ; RHS = GTZ\n");
              changed |= conju.removeJoin(
                  {}, {Constraint::get(-factorized.evidence - 1)});
              DEBUG(4, "Adding that " << factorized.evidence << " < 0\n"
                                      << conju << NL);
              break;
            }
            case SIGN::GTZ: {
              DEBUG(4, "evidence = UNKNOWN ==> GTZ; QUO = GTZ; RHS = GTZ\n");
              changed |= conju.removeJoin(
                  {}, {Constraint::get(factorized.evidence - 1)});
              DEBUG(4, "Adding that " << factorized.evidence << " > 0\n"
                                      << conju << NL);
              break;
            }
            case SIGN::UNKNOWN: { // (evidence = UNKNOWN) * (QUO = UNKNOWN) =
                                  // (RHS > 0)
              Conjunction ltzltz =
                  conju; // Split, either evidence = QUO = ( GEZ or LTZ )
              ltzltz.removeJoin({}, {Constraint::get(-factorized.evidence - 1),
                                     Constraint::get(-factorized.quo - 1)});
              conju.removeJoin({}, {Constraint::get(factorized.evidence - 1),
                                    Constraint::get(factorized.quo - 1)});
              DEBUG(4, "Splitting:\n\t" << ltzltz << NL << conju << NL);
#ifdef SCRIPT_CONTROL
              cout << ltzltz << NL << conju << NL;
              exit(0);
#else
              ret.push_back(ltzltz);
#endif
              break;
            }
            default: {
              assert(false);
              break;
            }
            }
          } else if (sQUO == SIGN::UNKNOWN) { // (evidence != UNKNOWN) * (QUO ==
                                              // UNKNOWN) = (RHS > 0)
            switch (sEVI) {
            case SIGN::LTZ: { // (evidence = LTZ) * (QUO = UNKNOWN ==> LTZ) =
                              // (RHS = GTZ)
              DEBUG(4, "evidence = LTZ; QUO = UNKNOWN ==> LTZ; RHS = GTZ\n");
              changed |=
                  conju.removeJoin({}, {Constraint::get(-factorized.quo - 1)});
              DEBUG(4, "Adding that " << factorized.quo << " < 0\n"
                                      << conju << NL);
              break;
            }
            case SIGN::GTZ: {
              DEBUG(4, "evidence = GTZ; QUO = UNKNOWN ==> GTZ; RHS = GTZ\n");
              changed |= conju.removeJoin(
                  {}, {Constraint::get(factorized.evidence - 1)});
              DEBUG(4, "Adding that " << factorized.evidence << " > 0\n"
                                      << conju << NL);
              break;
            }
            default:
              assert(false);
              break;
            }
          }
        } else { // sRHS == LTZ
          assert(sRHS == SIGN::LTZ);

          if (sEVI ==
              SIGN::UNKNOWN) { // (evidence = UNKNOWN) * (QUO) = (RHS < 0 / LTZ)
            switch (sQUO) {
            case SIGN::LTZ: { // (evidence = UNKNOWN) * (QUO < 0) = (RHS > 0)
              DEBUG(4, "evidence = UNKNOWN ==> GTZ; QUO = LTZ; RHS = LTZ\n");
              changed |= conju.removeJoin(
                  {}, {Constraint::get(factorized.evidence - 1)});
              DEBUG(4, "Adding that " << factorized.evidence << " > 0\n"
                                      << conju << NL);
              break;
            }
            case SIGN::GTZ: {
              DEBUG(4, "evidence = UNKNOWN ==> LTZ; QUO = GTZ; RHS = LTZ\n");
              changed |= conju.removeJoin(
                  {}, {Constraint::get(-factorized.evidence - 1)});
              DEBUG(4, "Adding that " << factorized.evidence << " < 0\n"
                                      << conju << NL);
              break;
            }
            case SIGN::UNKNOWN: { // (evidence = UNKNOWN) * (QUO = UNKNOWN) =
                                  // (RHS < 0 / LTZ)
              Conjunction ltzgtz =
                  conju; // Split, either evidence = QUO = ( GEZ or LTZ )
              ltzgtz.removeJoin({}, {Constraint::get(-factorized.evidence - 1),
                                     Constraint::get(factorized.quo - 1)});
              changed |= conju.removeJoin(
                  {}, {Constraint::get(factorized.evidence - 1),
                       Constraint::get(-factorized.quo - 1)});
              DEBUG(4, "Splitting:\n\t" << ltzgtz << NL << conju << NL);
#ifdef SCRIPT_CONTROL
              cout << ltzgtz << NL << conju << NL;
              exit(0);
#else
              ret.push_back(ltzgtz);
#endif
              break;
            }
            default: {
              assert(false);
              break;
            }
            }
          } else if (sQUO == SIGN::UNKNOWN) { // (evidence != UNKNOWN) * (QUO ==
                                              // UNKNOWN) = (RHS < 0 / LTZ)
            switch (sEVI) {
            case SIGN::LTZ: { // (evidence = LTZ) * (QUO = UNKNOWN ==> LTZ) =
                              // (RHS = LTZ)
              DEBUG(4, "evidence = LTZ; QUO = UNKNOWN ==> GTZ; RHS = LTZ\n");
              changed |=
                  conju.removeJoin({}, {Constraint::get(factorized.quo - 1)});
              DEBUG(4, "Adding that " << factorized.quo << " > 0\n"
                                      << conju << NL);
              break;
            }
            case SIGN::GTZ: {
              DEBUG(4, "evidence = GTZ; QUO = UNKNOWN ==> LTZ; RHS = LTZ\n");
              changed |= conju.removeJoin(
                  {}, {Constraint::get(-factorized.evidence - 1)});
              DEBUG(4, "Adding that " << factorized.evidence << " < 0\n"
                                      << conju << NL);
              break;
            }
            default: {
              assert(false);
              break;
            }
            }
          }
        }
      } else { // We have RHS == GEZ or LEZ
        if (sRHS == SIGN::GEZ) {
          if (sEVI ==
              SIGN::UNKNOWN) { // (evidence = UNKNOWN) * (QUO) = (RHS > 0)
            switch (sQUO) {
            case SIGN::LTZ: { // (evidence = UNKNOWN) * (QUO < 0) = (RHS >= 0)
              DEBUG(4, "evidence = UNKNOWN ==> LEZ; QUO = LTZ; RHS = GTZ\n");
              changed |=
                  conju.removeJoin({}, {Constraint::get(-factorized.evidence)});
              DEBUG(4, "Adding that " << factorized.evidence << LE << 0 << NL
                                      << conju << NL);
              break;
            }
            case SIGN::GTZ: {
              DEBUG(4, "evidence = UNKNOWN ==> GEZ; QUO = GTZ; RHS = GTZ\n");
              changed |=
                  conju.removeJoin({}, {Constraint::get(factorized.evidence)});
              DEBUG(4, "Adding that " << factorized.evidence << GE << 0 << NL
                                      << conju << NL);
              break;
            }
            default: {
              break;
            }
            }
          } else if (sQUO == SIGN::UNKNOWN) { // (evidence != UNKNOWN) * (QUO ==
                                              // UNKNOWN) = (RHS >= 0)
            switch (sEVI) {
            case SIGN::LTZ: { // (evidence = LTZ) * (QUO = UNKNOWN ==> LEZ) =
                              // (RHS = GEZ)
              DEBUG(4, "evidence = LTZ; QUO = UNKNOWN ==> LEZ; RHS = GTZ\n");
              changed |=
                  conju.removeJoin({}, {Constraint::get(-factorized.quo)});
              DEBUG(4, "Adding that " << factorized.quo << LE << NL << conju
                                      << NL);
              break;
            }
            case SIGN::GTZ: {
              DEBUG(4, "evidence = GTZ; QUO = UNKNOWN ==> GEZ; RHS = GEZ\n");
              changed |=
                  conju.removeJoin({}, {Constraint::get(factorized.evidence)});
              DEBUG(4, "Adding that " << factorized.evidence << GE << 0 << NL
                                      << conju << NL);
              break;
            }
            default:
              break;
            }
          }
        } else { // sRHS == LEZ
          assert(sRHS == SIGN::LEZ);

          if (sEVI == SIGN::UNKNOWN) { // (evidence = UNKNOWN) * (QUO) = (RHS <=
                                       // 0 / LEZ)
            switch (sQUO) {
            case SIGN::LTZ: { // (evidence = UNKNOWN) * (QUO < 0) = (RHS <= 0)
              DEBUG(4, "evidence = UNKNOWN ==> GEZ; QUO = LTZ; RHS = LEZ\n");
              changed |=
                  conju.removeJoin({}, {Constraint::get(factorized.evidence)});
              DEBUG(4, "Adding that " << factorized.evidence << GE << 0 << NL
                                      << conju << NL);
              break;
            }
            case SIGN::GTZ: {
              DEBUG(4, "evidence = UNKNOWN ==> LEZ; QUO = GTZ; RHS = LEZ\n");
              changed |=
                  conju.removeJoin({}, {Constraint::get(-factorized.evidence)});
              DEBUG(4, "Adding that " << factorized.evidence << GE << 0 << NL
                                      << conju << NL);
              break;
            }
            default:
              break;
            }
          } else if (sQUO == SIGN::UNKNOWN) { // (evidence != UNKNOWN) * (QUO ==
                                              // UNKNOWN) = (RHS <= 0 / LTZ)
            switch (sEVI) {
            case SIGN::LTZ: { // (evidence = LTZ) * (QUO = UNKNOWN ==> LTZ) =
                              // (RHS = LTZ)
              DEBUG(4, "evidence = LTZ; QUO = UNKNOWN ==> GEZ; RHS = LEZ\n");
              changed |=
                  conju.removeJoin({}, {Constraint::get(factorized.quo)});
              DEBUG(4, "Adding that " << factorized.quo << GE << 0 << NL
                                      << conju << NL);
              break;
            }
            case SIGN::GTZ: {
              DEBUG(4, "evidence = GTZ; QUO = UNKNOWN ==> LEZ; RHS = LEZ\n");
              changed |=
                  conju.removeJoin({}, {Constraint::get(-factorized.evidence)});
              DEBUG(4, "Adding that " << factorized.evidence << LE << 0 << NL
                                      << conju << NL);
              break;
            }
            default: {
              assert(false);
              break;
            }
            }
          }
        }
      }
    } else { // RHS == UNKNOWN
      if ((sEVI != SIGN::UNKNOWN) && (sQUO != SIGN::UNKNOWN)) {
        if (0 ==
            (sEVI & sQUO & (~SIGN::ZERO))) { // Opposite signs of sEVI and sREM
          if ((sEVI | sQUO) & SIGN::ZERO) {
            sRHS = SIGN::LEZ;
            changed |= conju.removeJoin({}, {Constraint::get(-factorized.rhs)});
          } else {
            sRHS = SIGN::LTZ;
            changed |=
                conju.removeJoin({}, {Constraint::get(-factorized.rhs - 1)});
          }
        } else { // Same sign, then RHS is non-negative
          if ((sEVI | sQUO) & SIGN::ZERO) {
            sRHS = SIGN::GEZ;
            changed |= conju.removeJoin({}, {Constraint::get(factorized.rhs)});
          } else {
            sRHS = SIGN::GTZ;
            changed |=
                conju.removeJoin({}, {Constraint::get(factorized.rhs - 1)});
          }
        }
      }
    }
    // Sanity check:
    // If there are unknowns, skip this check
    if (!(sRHS == SIGN::UNKNOWN || sEVI == SIGN::UNKNOWN ||
          sQUO == SIGN::UNKNOWN)) {
      // Is the RHS != 0 and LHS == 0 or RHS == 0 and LHS != 0?
      bool lhsEzero = (0 != ((sEVI | sQUO) & SIGN::ZERO));
      bool lhsPositive = (((sEVI & SIGN::GTZ) && (sQUO & SIGN::GTZ)) ||
                          ((sEVI & SIGN::LTZ) && (sQUO & SIGN::LTZ)));
      bool rhsEzero = (0 != (sRHS & SIGN::ZERO));
      bool rhsPositive = (0 != (sRHS & SIGN::GTZ));
      if (rhsPositive != lhsPositive) {
        if (!(rhsEzero && lhsEzero)) {
          DEBUG(2, "SIGN(RHS)" << NE << "SIGN(LHS) and at least one is " << NE
                               << 0 << NL);
          _returnAbsurd();
          return true;
        }
        changed |=
            conju.removeJoin({}, {Constraint::get(factorized.rhs, true)});
        if ((sEVI & SIGN::ZERO) != (sQUO & SIGN::ZERO)) {
          if (sEVI & SIGN::ZERO)
            changed |= conju.removeJoin(
                {}, {Constraint::get(factorized.evidence, true)});
          else
            changed |=
                conju.removeJoin({}, {Constraint::get(factorized.quo, true)});
        }
      }
      if (lhsEzero != rhsEzero) {
        if (!(sRHS & SIGN::ZERO)) {
          if (sRHS & SIGN::GTZ) {
            DEBUG(4, "Making RHS " << factorized.rhs << GE << "1!!\n");
            changed |=
                conju.removeJoin({}, {Constraint::get(factorized.rhs - 1)});
          } else {
            DEBUG(4, "Making RHS " << factorized.rhs << LE << "-1!!\n");
            changed |=
                conju.removeJoin({}, {Constraint::get(-factorized.rhs - 1)});
          }
        } else {
          if (!(sEVI & SIGN::ZERO)) {
            if (sEVI & SIGN::GTZ) {
              DEBUG(4, "Making EVI " << factorized.evidence << GE << "1!!\n");
              changed |= conju.removeJoin(
                  {}, {Constraint::get(factorized.evidence - 1)});
            } else {
              DEBUG(4, "Making EVI " << factorized.evidence << LE << "-1!!\n");
              changed |= conju.removeJoin(
                  {}, {Constraint::get(-factorized.evidence - 1)});
            }
          }
          if (!(sQUO & SIGN::ZERO)) {
            if (sQUO & SIGN::GTZ) {
              DEBUG(4, "Making QUO " << factorized.quo << GE << "1!!\n");
              changed |=
                  conju.removeJoin({}, {Constraint::get(factorized.quo - 1)});
            } else {
              DEBUG(4, "Making QUO " << factorized.quo << LE << "-1!!\n");
              changed |=
                  conju.removeJoin({}, {Constraint::get(-factorized.quo - 1)});
            }
          }
        }
      }
      if (lhsPositive && (sRHS & SIGN::LTZ)) {
        if (sRHS == SIGN::LTZ) {
          DEBUG(0, "LHS " << GE << "0, and RHS < 0!! Absurd!\n");
          _returnAbsurd();
          return true;
        }
        DEBUG(4, "LHS " << GE << "0, and RHS" << LE << "0 ==> RHS is ZERO\n");
        changed |=
            conju.removeJoin({}, {Constraint::get(factorized.rhs, true)});
      } else if ((!lhsPositive) && (sRHS & SIGN::GTZ)) {
        if (sRHS == SIGN::GTZ) {
          DEBUG(0, "LHS " << LE << "0, and RHS > 0!! Absurd!\n");
          _returnAbsurd();
          return true;
        }
        DEBUG(4, "LHS " << LE << "0, and RHS" << GE << "0 ==> RHS is ZERO\n");
        changed |=
            conju.removeJoin({}, {Constraint::get(factorized.rhs, true)});
      }
    }

    if ((sEVI == SIGN::UNKNOWN) || (sRHS == SIGN::UNKNOWN)) {
      DEBUG(4, "FIXME: TODO: Test evi - rhs and evi + rhs and check if both "
               "have known information\n");
      // TODO: Test evi - rhs and evi + rhs and check if both have known
      // information
    } else if (sEVI & (SIGN::GTZ | SIGN::LTZ)) {
      testResult sEviRhs;
      if (sEVI & sRHS & (~SIGN::ZERO)) {
        sEviRhs = tester->test(
            factorized.evidence -
            factorized.rhs); // rhs and evi have same sign (G?Z or L?Z)
      } else {
        sEviRhs = tester->test(
            factorized.evidence +
            factorized.rhs); // rhs and evi have distinct sign (G?Z and L?Z)
      }
      if (sEviRhs.sign != SIGN::UNKNOWN) {
        if (sEviRhs.sign & sEVI &
            (~SIGN::ZERO)) { // evi - rhs has same sign of evi. Thus |evi| >=
                             // |rhs| and |quo| <= 1
          if (sEviRhs.sign & SIGN::ZERO) { //|evi| >= |rhs| ===> |quo| <= 1
            switch (sQUO) {
            case SIGN::UNKNOWN: {
              Conjunction plus = conju, minus = conju;
              plus.removeJoin(
                  {}, {Constraint::get(factorized.quo - 1, true)}); // quo = 1
              minus.removeJoin(
                  {}, {Constraint::get(factorized.quo + 1, true)}); // quo = -1
              changed |= conju.removeJoin(
                  {}, {Constraint::get(factorized.quo, true)}); // quo = 0
              DEBUG(4, minus << NL << conju << NL << plus << NL);
#ifdef SCRIPT_CONTROL
              cout << minus << NL << conju << NL << plus << NL;
              cout.flush();
              exit(0);
#else
              ret.push_back(plus);
              ret.push_back(minus);
#endif
              break;
            }
            case SIGN::LTZ: {
              changed |= conju.removeJoin(
                  {}, {Constraint::get(-factorized.quo + 1, true)}); //-quo = -1
              DEBUG(4, conju << NL);
              break;
            }
            case SIGN::LEZ: {
              changed |= conju.removeJoin(
                  {}, {Constraint::get(-factorized.quo + 1)}); //-1 <= -quo <= 0
              DEBUG(4, conju << NL);
              break;
            }
            case SIGN::GTZ: {
              changed |= conju.removeJoin(
                  {}, {Constraint::get(factorized.quo - 1, true)}); // quo = 1
              DEBUG(4, conju << NL);
              break;
            }
            case SIGN::GEZ: {
              changed |= conju.removeJoin(
                  {}, {Constraint::get(factorized.quo - 1)}); // 0 <= quo <= 1
              DEBUG(4, conju << NL);
              break;
            }
            case SIGN::ZERO: {
              DEBUG(4, "TODO\n");
              break;
            }
            default:
              break;
            }
          } else { //|evi| > |RHS| ===> RHS = 0 and QUO = 0
            if (((sQUO != SIGN::UNKNOWN) && (!(sQUO & SIGN::ZERO))) ||
                ((sRHS != SIGN::UNKNOWN) && (!(sRHS & SIGN::ZERO)))) {
              DEBUG(4, "|evi| > |RHS|, but (RHS or QUO) " << NE << 0 << NL);
              returnAbsurd();
              return true;
            }
            changed |= conju.removeJoin(
                {}, {Constraint::get(factorized.quo, true),
                     Constraint::get(factorized.rhs, true)}); // quo = 1
            DEBUG(4, "|evi| > |RHS|, thus 0 = RHS = QUO\n" << conju << NL);
          }
        } else { //|RHS| >= |evidence|, thus |QUO| <= |RHS|
          ex diff = 0;
          if (!(sEviRhs.sign & SIGN::ZERO))
            diff = 1;
          switch (sQUO) {
          case LTZ:
          case LEZ: {
            if (sRHS & SIGN::GTZ) {
              changed |= conju.removeJoin(
                  {},
                  {Constraint::get(factorized.quo + factorized.rhs - diff)});
              DEBUG(4, "|evi|" << LE << "|RHS| (" << factorized.rhs << " ["
                               << sRHS << "] ), thus QUO("
                               << factorized.quo - diff << " [" << sQUO << "] )"
                               << GE << -factorized.rhs << NL << conju << NL);
            } else {
              changed |= conju.removeJoin(
                  {},
                  {Constraint::get(factorized.quo - factorized.rhs - diff)});
              DEBUG(4, "|evi|" << LE << "|RHS| (" << factorized.rhs << " ["
                               << sRHS << "] ), thus QUO("
                               << factorized.quo - diff << " [" << sQUO
                               << " ] )" << GE << factorized.rhs << NL << conju
                               << NL);
            }
            break;
          }
          case GTZ:
          case GEZ: {
            if (sRHS & SIGN::GTZ) {
              changed |= conju.removeJoin(
                  {},
                  {Constraint::get(factorized.rhs - factorized.quo + diff)});
              DEBUG(4, "|evi|" << LE << "|RHS| (" << factorized.rhs << " ["
                               << sRHS << "]), thus QUO("
                               << factorized.quo + diff << " [" << sQUO << "] )"
                               << LE << factorized.rhs << NL << conju << NL);
            } else {
              changed |= conju.removeJoin(
                  {},
                  {Constraint::get(-factorized.rhs - factorized.quo + diff)});
              DEBUG(4, "|evi|" << LE << "|RHS| (" << factorized.rhs << " ["
                               << sRHS << "] ), thus QUO("
                               << factorized.quo + diff << " [" << sQUO << "] )"
                               << LE << -factorized.rhs << NL << conju << NL);
            }
            break;
          default:
            break;
          }
          }
        }
      }
    }

    if ((sQUO == SIGN::UNKNOWN) || (sRHS == SIGN::UNKNOWN)) {
      DEBUG(4, "FIXME: TODO: Test QUO - rhs and QUO + rhs and check if both "
               "have known information\n");
      // TODO: Test QUO - rhs and QUO + rhs and check if both have known
      // information
    } else if (sQUO & (SIGN::GTZ | SIGN::LTZ)) {
      testResult sRemRhs;
      if (sQUO & sRHS & (~SIGN::ZERO)) {
        sRemRhs = tester->test(factorized.quo - factorized.rhs);
        // QUO and rhs have same sign (G?Z or L?Z)
      } else {
        sRemRhs = tester->test(factorized.quo + factorized.rhs);
        // QUO and rhs have distinct sign (G?Z and L?Z)
      }
      if (sRemRhs.sign != SIGN::UNKNOWN) {
        if (sRemRhs.sign & sEVI & (~SIGN::ZERO)) {
          // QUO - rhs has same sign of QUO. Thus |QUO| >= |rhs| and |evi| <= 1
          if (sRemRhs.sign & SIGN::ZERO) { //|QUO| >= |rhs| ===> |evi| <= 1
            switch (sEVI) {
            case SIGN::UNKNOWN: {
              Conjunction plus = conju, minus = conju;
              plus.removeJoin({}, {Constraint::get(factorized.evidence - 1,
                                                   true)}); // evidence = 1
              minus.removeJoin({}, {Constraint::get(factorized.evidence + 1,
                                                    true)}); // evidence=-1
              changed |= conju.removeJoin(
                  {},
                  {Constraint::get(factorized.evidence, true)}); // evidence = 0
              DEBUG(4, minus << NL << conju << NL << plus << NL);
#ifdef SCRIPT_CONTROL
              cout << minus << NL << conju << NL << plus << NL;
              cout.flush();
              exit(0);
#else
              ret.push_back(minus);
              ret.push_back(plus);
#endif
              break;
            }
            case SIGN::LTZ: {
              changed |= conju.removeJoin(
                  {}, {Constraint::get(-factorized.evidence + 1,
                                       true)}); //-evidence = -1
              DEBUG(4, conju << NL);
              break;
            }
            case SIGN::LEZ: {
              changed |= conju.removeJoin(
                  {}, {Constraint::get(-factorized.evidence +
                                       1)}); //-1 <= -evidence <= 0
              DEBUG(4, conju << NL);
              break;
            }
            case SIGN::GTZ: {
              changed |=
                  conju.removeJoin({}, {Constraint::get(factorized.evidence - 1,
                                                        true)}); // evidence = 1
              DEBUG(4, conju << NL);
              break;
            }
            case SIGN::GEZ: {
              changed |= conju.removeJoin(
                  {}, {Constraint::get(factorized.evidence -
                                       1)}); // 0 <= evidence <= 1
              DEBUG(4, conju << NL);
              break;
            }
            case SIGN::ZERO: {
              DEBUG(4, "TODO\n");
              break;
            }
            default:
              break;
            }
          } else { //|QUO| > |RHS| ===> evi = 0 and QUO = 0
            if (((sEVI != SIGN::UNKNOWN) && (!(sEVI & SIGN::ZERO))) ||
                ((sRHS != SIGN::UNKNOWN) && (!(sRHS & SIGN::ZERO)))) {
              DEBUG(4, "|QUO| > |RHS|, but (EVI or QUO) " << NE << 0 << NL);
              returnAbsurd();
              return true;
            }
            changed |= conju.removeJoin(
                {}, {Constraint::get(factorized.evidence, true),
                     Constraint::get(factorized.rhs, true)}); // quo = 1
            DEBUG(4, "|evi| > |RHS|, thus 0 = RHS = QUO\n" << conju << NL);
          }
        } else {
          //|RHS| >= |evidence|, thus |QUO| <= |RHS|
          ex diff = 0;
          if (!(sRemRhs.sign & SIGN::ZERO))
            diff = 1;
          switch (sEVI) {
          case LTZ:
          case LEZ: {
            if (sRHS & SIGN::GTZ) {
              changed |= conju.removeJoin(
                  {}, {Constraint::get(factorized.evidence + factorized.rhs -
                                       diff)});
              DEBUG(4, "|QUO|" << LE << "|RHS| (" << factorized.rhs << sRHS
                               << "), thus evidence("
                               << factorized.evidence - diff << " [" << sQUO
                               << "])" << GE << -factorized.rhs << NL << conju
                               << NL);
            } else {
              changed |= conju.removeJoin(
                  {}, {Constraint::get(factorized.evidence - factorized.rhs -
                                       diff)});
              DEBUG(4, "|QUO|" << LE << "|RHS| (" << factorized.rhs << sRHS
                               << "), thus evidence("
                               << factorized.evidence - diff << " [" << sQUO
                               << "])" << GE << factorized.rhs << NL << conju
                               << NL);
            }
            break;
          }
          case GTZ:
          case GEZ: {
            if (sRHS & SIGN::GTZ) {
              changed |= conju.removeJoin(
                  {}, {Constraint::get(factorized.rhs - factorized.evidence +
                                       diff)});
              DEBUG(4, "|QUO|" << LE << "|RHS| (" << factorized.rhs << " ["
                               << sRHS << "] ), thus evidence("
                               << factorized.evidence + diff << " [" << sQUO
                               << "] )" << LE << factorized.rhs << NL << conju
                               << NL);
            } else {
              changed |= conju.removeJoin(
                  {}, {Constraint::get(-factorized.rhs - factorized.evidence +
                                       diff)});
              DEBUG(4, "|QUO|" << LE << "|RHS| (" << factorized.rhs << " ["
                               << sRHS << "] ), thus evidence("
                               << factorized.evidence + diff << " [" << sQUO
                               << "] )" << LE << -factorized.rhs << NL << conju
                               << NL);
            }
            break;
          default:
            break;
          }
          }
        }
      }
    }
  } // end for
  return changed;
}

Simplifier::Simplifier(Conjunction &s) : conju(s) {}
void Simplifier::run() {
  while (true) {
    conju.detectEqs();
    DEBUG(0, "System (size: " << conju.size() << ") is:\n" << conju << NL);
    do {
      sanityCheck();
      DEBUG(5, conju << NL);
      build_tester();
    } while (eqs_affinize() || eqs_pattern_matching() ||
             gaussian_replacement());

    if (conju.size() < 30) {
      if (add_affine_planes()) {
        sanityCheck();
        DEBUG(0, "System after adding affine planes:\n" << conju);
        build_tester();
      }
    } else {
      if (getRoots()) {
        DEBUG(0, "System after roots search:\n" << conju);
        build_tester();
      }
    }

    if (normalize()) {
      DEBUG(0, "System after obtaining roots:\n" << conju);
      sanityCheck();
      build_tester();
    }

    if (conju.size() < 100) {
      if (tightening()) {
        DEBUG(0, "System after tightening constraints:\n" << conju);
        sanityCheck();
        build_tester();
      }
    }
    DEBUG(0, "System after treating equalities (size: " << conju.size()
                                                        << "):\n"
                                                        << conju);
    if (!conju.hasVariables()) {
      DEBUG(0, "Done removing all variables");
      sanityCheck();
      getRoots();
      normalize();
      DEBUG(0, "System after roots search:\n" << conju);
      while (tightening()) {
        getRoots();
        conju.detectEqs();
        DEBUG(0, "Could still reduce simplified system to:\n" << conju);
        build_tester();
      }
      sanityCheck();
      ret.push_back(conju);
      return;
    }

    sanityCheck();
    if (conju.hasEqs()) {
      DEBUG(
          0,
          "Did not eliminate all equalities, convert them to two inequalities\n"
              << conju);

      Constraints pm;
      for (cc e : conju.eqs) {
        pm.insert(Constraint::get(e->exp));
        pm.insert(Constraint::get(-e->exp));
      }
      conju.removeJoin({}, pm);
    }
    DEBUG(0, "Giving the system:\n" << conju);

    testResult val = tester->test(ex(-1), false);
    switch (val.sign) {
    case SIGN::LTZ: {
      if (val.distance == 1.0)
        break;
      /* no break */
      cerr << "Got SIGN " << val << " to expression (-1)!!! ABSURD!!\n";
      tester->printResult(cerr, true);
      returnAbsurd();
      return;
    }
    case SIGN::LEZ:
    case SIGN::GTZ:
    case SIGN::GEZ:
    case SIGN::ZERO:
    case SIGN::ABSURD: {
      cerr << "Got SIGN " << val << " to expression (-1)!!! ABSURD!!\n";
      tester->printResult(cerr, true);
      returnAbsurd();
      return;
    }
      /* no break */
    default:
      break;
    }

    if (conju.hasVariables()) {
      if (conju.hasEqs()) {
        for (cc c : conju.eqs) {
          conju.ineqs.insert(Constraint::get(c->exp));
          conju.ineqs.insert(Constraint::get(-c->exp));
        }
        conju.eqs.clear();
      }
      DEBUG(5, conju << NL)

      Motzkin();
    }
  }
}

ex Simplifier::compose(const testResult tr, const ex &tested) {
  switch (tr.sign) {
  case SIGN::GTZ:
    return expand(tested - (long)(std::ceil((float)tr.distance - MAX_ERROR)));
  case SIGN::LEZ:
    return expand(-tested);
  case SIGN::LTZ:
    return expand(-tested - (long)(std::ceil((float)tr.distance - MAX_ERROR)));
  case SIGN::ABSURD:
    return (-1);
  default:
    break;
  }
  assertM(tr.distance > (-1.0000000000000000000 + MAX_ERROR),
          tested << " == " << tr);
  return tested;
}

bool Simplifier::proved(const testResult tr) const {
  switch (tr.sign) {
  case SIGN::UNKNOWN:
  case SIGN::LEZ:
  case SIGN::LTZ:
    return false;
  default:
    break;
  }
  return true;
}

// bool Simplifier::precision_increase(){
//  bool ret = false;
//  ret |= tightening();
//  ret |= normalize();
//  return ret;
//}

bool Simplifier::eqs_pattern_matching() {
  bool changed = false;
  Constraints newEqs, delEqs;
  for (cc eq : conju.eqs) {
    DEBUG(5, "Testing equality " << eq << NL);

    for (const ex &p : conju.pars) {
      int deg = eq->exp.degree(p);
      if (deg == 0)
        continue;

      for (int ud = 1; ud <= deg; ud++) {
        ex term = expand(pow(p, ud));
        DEBUG(6, "Testing " << p << '^' << ud << NL);
        ex lhs = quo(eq->exp, term, p);
        ex rhs = rem(eq->exp, term, p);
        if (is_a<numeric>(lhs))
          break;

        testResult ts = tester->test(term);
        DEBUG(5, '\t' << term << " == " << ts << NL);
        switch (ts.sign) {
        case SIGN::ABSURD: {
          returnAbsurd();
          return false;
        }
          /* no break */

        case SIGN::ZERO: {
          changed |= conju.eqs.insert(Constraint::get(lhs, true)).second;
          changed |= conju.eqs.insert(Constraint::get(term, true)).second;
          changed |= conju.eqs.insert(Constraint::get(rhs, true)).second;
          continue;
        }
          /* no break */
        case SIGN::UNKNOWN:
          continue;
          break;
        case SIGN::GEZ:
        case SIGN::GTZ:
          break;
        default:
          term = expand(-term);
          lhs = expand(-lhs);
        }
        DEBUG(5, '\t' << eq << " ====> " << term << " * (" << lhs
                      << ") = " << -rhs << NL);
        /*Now we have that term >= 0.
         * To test |term| >= |rhs| we test if term +- rhs >= 0 depending on sign
         * of rhs */
        testResult rhsS = tester->test(rhs);
        DEBUG(5, '\t' << rhs << " == " << rhsS << NL);
        ex toTest = term;
        switch (rhsS.sign) {
        case SIGN::ABSURD: {
          returnAbsurd();
          return false;
        }

          /* no break */
        case SIGN::ZERO: {
          changed |= conju.eqs.insert(Constraint::get(lhs, true)).second;
          changed |= conju.eqs.insert(Constraint::get(term, true)).second;
          changed |= conju.eqs.insert(Constraint::get(rhs, true)).second;
          DEBUG(5, '\t' << rhs << " = " << lhs << " = " << term << " = 0\n");
          continue;
        }
          /* no break */
        case SIGN::UNKNOWN:
          continue;
        case SIGN::GEZ:
        case SIGN::GTZ:
          toTest = expand(term - rhs);
          break;
        case SIGN::LEZ:
        case SIGN::LTZ:
          toTest = expand(term + rhs);
          break;
        default:
          assert(false);
        }
        testResult tr = tester->test(toTest);
        DEBUG(5, "\tTesting if bigger:" << toTest << " = " << tr << NL);
        switch (tr.sign) {
        case SIGN::ABSURD: {
          returnAbsurd();
          return false;
        }

          /* No break */
        case SIGN::UNKNOWN:
        case SIGN::LEZ:
        case SIGN::LTZ:
          continue;
        case SIGN::ZERO:
          DEBUG(5, "\t" << lhs << " = 1 & " << toTest << " = 0\n")

          changed |= conju.eqs.insert(Constraint::get(lhs - 1, true)).second;
          changed |= conju.eqs.insert(Constraint::get(toTest, true)).second;
          break;
        case SIGN::GEZ:
          changed |= conju.ineqs.insert(Constraint::get(toTest)).second;
          DEBUG(5, "\t" << toTest << " >= 0\n")

          if ((ts.distance > 0.0) || (ts.distance > 0.0)) {
            changed |= conju.ineqs.insert(Constraint::get(lhs - 1)).second;
            DEBUG(5, "\t" << lhs << " >= 1\n");
          }
          break;
        case SIGN::GTZ:
          changed |=
              conju.ineqs.insert(Constraint::get(compose(tr, toTest))).second;
          changed |= conju.eqs.insert(Constraint::get(lhs, true)).second;
          DEBUG(5, "\t" << lhs << " = 0 & " << toTest << " >= " << tr.distance
                        << "\n")
        }
      }
    }
  }
  return changed;
}

bool Simplifier::add_affine_planes() {
  return false;
  bool changed = false;
  Constraints toJoin;
  for (auto p1 = conju.pars.begin(), pEnd = conju.pars.end(); p1 != pEnd;
       p1++) {
    testResult tr = tester->test(*p1);
    DEBUG(5, "Testing " << *p1 << " got : " << tr << NL);
    if (tr.sign == SIGN::ABSURD) {
      returnAbsurd();
      return true;
    }

    if (tr.sign != SIGN::UNKNOWN)
      changed |= conju.ineqs.insert(Constraint::get(compose(tr, *p1))).second;

    for (auto p2 = std::next(p1); p2 != pEnd; p2++) {
      ex p1Pp2 = *p1 + *p2;
      tr = tester->test(p1Pp2);
      DEBUG(5, "Testing " << p1Pp2 << " got : " << tr << NL);

      if (tr.sign == SIGN::ABSURD) {
        returnAbsurd();
        return true;
      }

      if (tr.sign != SIGN::UNKNOWN)
        changed |=
            (conju.ineqs.insert(Constraint::get(compose(tr, p1Pp2))).second);

      ex p1Mp2 = *p1 - *p2;
      tr = tester->test(p1Mp2);
      DEBUG(5, "Testing " << p1Mp2 << " got : " << tr << NL);

      if (tr.sign == SIGN::ABSURD) {
        returnAbsurd();
        return true;
      }

      if (tr.sign != SIGN::UNKNOWN)
        changed |=
            (conju.ineqs.insert(Constraint::get(compose(tr, p1Mp2))).second);
    }
  }

  for (auto v1 = conju.vars.begin(), vEnd = conju.vars.end(); v1 != vEnd;
       v1++) {
    testResult tr = tester->test(*v1);
    DEBUG(5, "Testing " << *v1 << " got : " << tr << NL);

    if (tr.sign == SIGN::ABSURD) {
      returnAbsurd();
      return true;
    }

    if (tr.sign != SIGN::UNKNOWN)
      changed |= (conju.ineqs.insert(Constraint::get(compose(tr, *v1))).second);

    for (auto v2 = std::next(v1); v2 != vEnd; v2++) {
      ex v1Pv2 = *v1 + *v2;
      tr = tester->test(v1Pv2);
      DEBUG(5, "Testing " << v1Pv2 << " got : " << tr << NL);
      if (tr.sign == SIGN::ABSURD) {
        returnAbsurd();
        return true;
      }

      if (tr.sign != SIGN::UNKNOWN)
        changed |=
            (conju.ineqs.insert(Constraint::get(compose(tr, v1Pv2))).second);

      ex v1Mv2 = *v1 - *v2;
      DEBUG(5, "Testing " << v1Mv2 << " got : " << tr << NL);

      tr = tester->test(v1Mv2);
      if (tr.sign == SIGN::ABSURD) {
        returnAbsurd();
        return true;
      }

      if (tr.sign != SIGN::UNKNOWN)
        changed |=
            (conju.ineqs.insert(Constraint::get(compose(tr, v1Mv2))).second);
    }

    for (auto p1 = conju.pars.begin(), pEnd = conju.pars.end(); p1 != pEnd;
         p1++) {
      ex p1Pv1 = *p1 + *v1;
      DEBUG(5, "Testing " << p1Pv1 << " got : " << tr << NL);

      tr = tester->test(p1Pv1);
      if (tr.sign == SIGN::ABSURD) {
        returnAbsurd();
        return true;
      }

      if (tr.sign != SIGN::UNKNOWN)
        changed |=
            (conju.ineqs.insert(Constraint::get(compose(tr, p1Pv1))).second);

      ex p1Mv1 = *p1 - *v1;
      DEBUG(5, "Testing " << p1Mv1 << " got : " << tr << NL);

      tr = tester->test(p1Mv1);
      if (tr.sign == SIGN::ABSURD) {
        returnAbsurd();
        return true;
      }

      if (tr.sign != SIGN::UNKNOWN)
        changed |=
            (conju.ineqs.insert(Constraint::get(compose(tr, p1Mv1))).second);
    }
  }
  return changed;
}

bool Simplifier::tightening() {
  if (conju.size() < 2)
    return false;

  Constraints addExs, removeExs;
  DEBUG(0, "Tightening the system " << conju << NL);
  for (cc c : conju.ineqs) {
    Conjunction other = conju;
    bool r = other.removeJoin({c}, {});
    if (!r) {
      assertM(false,
              "Failed to remove an constraint from the duplicated system!!\n");
    }
    testResult tr = other.getTester()->test(c->exp);
    DEBUG(8, "Got " << tr << " when testing the constraint " << c
                    << " against the system\n"
                    << other << NL);
    switch (other.getTester()->test(c->exp).sign) {
    case SIGN::ABSURD:
    case SIGN::LTZ: {
      returnAbsurd();
      return false;
      break;
    }
    case SIGN::ZERO:
    case SIGN::LEZ: {
      removeExs.insert(c);
      addExs.insert(Constraint::get(c->exp, true));
      break;
    }
    case SIGN::GEZ: {
      if (!conju.hasVariables()) {
        conju.removeJoin({c}, {});
        build_tester();
        tightening();
        return true;
      }
      break;
    }
    case SIGN::GTZ: {
      if (!conju.hasVariables()) {
        conju.removeJoin({c}, {});
        build_tester();
        tightening();
        return true;
      }
      removeExs.insert(c);
      addExs.insert(Constraint::get(compose(tr, c->exp)));
      removeExs.insert(Constraint::get(c->exp));
      break;
    }
    case SIGN::UNKNOWN:
      break;
    }
  }

  if (addExs.empty() && removeExs.empty())
    return false;

  bool toret = conju.removeJoin(removeExs, addExs);
  return toret;
}

bool Simplifier::getRoots() {
  map<int, Constraints> constraintsBySize;
  int maxSize = 0, minSize = 99999999;
  for (cc c : conju.eqs) {
    if (is_a<add>(c->exp)) {
      int sz = c->exp.nops();
      maxSize = max(maxSize, sz);
      minSize = min(minSize, sz);
      constraintsBySize[sz].insert(c);
    } else {
      maxSize = max(maxSize, 1);
      minSize = min(minSize, 1);
      constraintsBySize[1].insert(c);
    }
  }
  for (cc c : conju.ineqs) {
    if (is_a<add>(c->exp)) {
      int sz = c->exp.nops();
      maxSize = max(maxSize, sz);
      minSize = min(minSize, sz);
      constraintsBySize[sz].insert(c);
    } else {
      maxSize = max(maxSize, 1);
      minSize = min(minSize, 1);
      constraintsBySize[1].insert(c);
    }
  }

  Conjunction nc(conju.vars, conju.pars, constraintsBySize[minSize],
                 conju.id());

  int removed = 0;
  while (minSize < maxSize) {
    minSize++;
    if (constraintsBySize.find(minSize) == constraintsBySize.end())
      continue;
    for (cc c : constraintsBySize[minSize]) {
      SchweighoferTester *nt = nc.getTester();
      testResult tr = nt->test(c->exp, false);
      DEBUG(4, "The expression " << c->exp << " is " << tr << NL);
      switch (tr.sign) {
      case SIGN::ABSURD: {
        returnAbsurd();
        return true;
      }
      case SIGN::GEZ:
      case SIGN::GTZ:
      case SIGN::ZERO: {
        removed++;
        DEBUG(7, "Remove the constraint " << c << " as it is implied to be "
                                          << tr << " by:\n"
                                          << nc << NL);
        continue;
      }
      default: {
        DEBUG(7, "The constraint " << c << " is not implied " << tr << " by:\n"
                                   << nc << NL);
        nc.removeJoin({}, {c});
      }
      }
    }
  }
  if (removed) {
    conju.eqs = nc.eqs;
    conju.ineqs = nc.ineqs;
    build_tester();
    DEBUG(4, "Removed " << removed
                        << " redundant constraints.\nThe system is now:"
                        << conju << NL);
    return true;
  }
  return false;
}

bool Simplifier::normalize() {
  // Eqs: If m(P) * lhs(P,V) = rhs(P,V), and |m| > |rhs|, that implies that lhs
  // = 0
  Constraints toAdd, toRemove;
  for (cc c : conju.ineqs) {
    bool simplified = false;
    if (is_a<symbol>(c->exp) or is_a<symbol>(expand(-c->exp))) {
      DEBUG(9, c->exp << " is a symbol. Can't do magic, (yet :)" << c << NL)
      continue;
    }
    ex lhs = factor(c->exp, factor_options::all);
    ex m_lhs = factor(expand(-c->exp), factor_options::all);
    if (is_a<power>(lhs) or (is_a<power>(m_lhs))) {
      DEBUG(4, c->exp << " is a power, or -power expression" << NL)
      bool neg_is_a_pow = is_a<power>(m_lhs);
      if (neg_is_a_pow) {
        DEBUG(4, -c->exp << " is a power" << NL)
        if (is_a<power>(lhs)) {
          cerr << "This makes no sense! " << lhs << " is a power, and so it is "
               << m_lhs << NL;
          throw "ohoh.";
        }
        lhs = move(m_lhs);
      }
      numeric n = ex_to<numeric>(lhs.op(1));
      if (not neg_is_a_pow) {

        if (n.is_odd()) {
          DEBUG(4, "Converting " << c->exp << GE << "0 to " << lhs.op(0) << GE
                                 << 0 << NL)
          toRemove.insert(c);
          toAdd.insert(Constraint::get(lhs.op(0)));
        }
      } else {
        toRemove.insert(c);
        if (n.is_even()) {
          toAdd.insert(Constraint::get(lhs.op(0), true));
        } else {
          toAdd.insert(Constraint::get(-(lhs.op(0))));
        }
      }
    } else if (!is_a<add>(lhs) or !is_a<add>(m_lhs)) {
      ex LHS;
      bool invert, keep = false;
      if (!is_a<add>(lhs)) {
        LHS = lhs;
        invert = false;
      } else {
        LHS = m_lhs;
        invert = true;
      }
      ex div = 1;
      for (const ex &e : LHS) {
        if (is_a<numeric>(e)) {
          numeric n = ex_to<numeric>(e);
          if ((n < -1.0) or (n > 1.0)) {
            div *= n;
            simplified = true;
            if (n < 0.0)
              invert = !invert;
          }
          continue;
        }
        testResult tr = tester->test(e);
        switch (tr.sign) {
        case SIGN::LEZ:
        case SIGN::GEZ:
        case SIGN::UNKNOWN: {
          keep = true;
          continue;
        }
        case SIGN::ABSURD: {
          cerr << "The expression " << e
               << " is both exclusively positive and negative\n";
          returnAbsurd();
          return false;
        }
        case SIGN::LTZ: {
          simplified = true;
          div *= e;
          invert = !invert;
          toAdd.insert(Constraint::get(compose(tr, e)));
          continue;
        }
        case SIGN::GTZ: {
          simplified = true;
          div *= e;
          toAdd.insert(Constraint::get(compose(tr, e)));
          continue;
        }
        case SIGN::ZERO: {
          simplified = true;
          toAdd.insert(Constraint::get(e, true));
          div = 1;
          break;
        }
        }
      }
      if (simplified) {
        DEBUG(0, "Removing " << c << NL);
        toRemove.insert(c);
        if ((keep) and (div != 1)) {
          ex newcst;
          if (!divide(LHS, div, newcst))
            assertM(false,
                    "Computed that " << div << " should divide " << LHS << NL);
          if (invert)
            newcst = -newcst;
          DEBUG(0, "Inserting " << newcst << GE << 0 << NL);
          toAdd.insert(Constraint::get(newcst));
        }
      }
    }

    numeric df = 1;
    bool negate = false;
    bool factored = false;
    while (df <= 20) {
      lhs = factor(expand(c->exp + df));
      if (is_a<mul>(lhs) or is_a<power>(lhs)) {
        factored = true;
        break;
      }
      lhs = factor(expand(c->exp - df));
      if (is_a<mul>(lhs) or is_a<power>(lhs)) {
        factored = true;
        negate = true;
        break;
      }
      df++;
    }

    if (factored) {
      DEBUG(4, c << " = " << lhs << GE << df << NL);
      if (is_a<power>(lhs)) {
        DEBUG(0, "FIX ME!!!! Nice things to do with power: " << lhs << GE << df
                                                             << "!!!\n\n");
      } else {
        assert(is_a<mul>(lhs));
        DEBUG(0, lhs << " has been factored!!!");
        for (const ex &e : lhs) {
          testResult tr = tester->test(e);
          DEBUG(0, "The sign of:" << e << " is: " << tr);
          if (tr.sign == SIGN::ABSURD) {
            DEBUG(0, "Abs!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!");
            returnAbsurd();
            return false;
          }
          DEBUG(4, "Testing if |" << e << '|' << GE << '|' << df << "|\n");
          if (tr.distance >= df.to_double()) {
            if (tr.sign & SIGN::GTZ) {
              DEBUG(4, "Got that " << e << tr << GE << df << NL);
              toAdd.insert(Constraint::get(compose(tr, e)));
              ex q;
              if (!divide(lhs, e, q))
                assert(false);
              if (negate)
                toAdd.insert(Constraint::get(expand(q)));
              else
                toAdd.insert(Constraint::get(expand(q - 1)));
              toRemove.insert(c);
              break;
            }
          }
        }
      }
    }
  }
  return conju.removeJoin(toRemove, toAdd);
}

Simplifier::~Simplifier() { clear(); }

void Simplifier::clear() {
  if (nullptr != tester) {
    delete tester;
    tester = nullptr;
  }
}

bool Simplifier::gaussian_replacement(bool usePars) {
  DEBUG(4, "System size:" << conju.size() << NL);
  if (conju.eqs.empty())
    return false;
  cc c = nullptr;
  size_t nops = 99999;
  for (cc eq : conju.eqs) {
    if (is_a<add>(eq->exp)) {
      if (eq->exp.nops() < nops) {
        c = eq;
        nops = eq->exp.nops();
      }
      continue;
    }
    c = eq;
    break;
  }
  DEBUG(4, "Entering Gaussian replacement\n");
  Constraints toRemove;
  exset ineqs, eqs;
  DEBUG(4, "Testing eliminating equality: " << c << NL);

  int sysVarsDegree = 999, generatedVarsDegree = 999, sysDegree = 999,
      generatedDegree = 999;
  bool cleanIsolation = false;
  ex eliminated = 0;
  /* Selection of symbol to isolate, preferences:
   *  Replace a variable to a parameter.
   *  Generated system has lowest degree in variables
   *  Generated constraints has lowest degree in variables
   *  Generated system has lowest degree (including parameters)
   *  Generated constraints has lowest (including parameters)
   *  Could isolate the variable with a numeric quotient in the equality
   *   */

  Symbols &toTest =
      ((conju.varsDegree(c->exp) == 0) or usePars) ? conju.pars : conju.vars;
  for (const ex &v : toTest) {
    if (quo(c->exp, v, v) == 0)
      continue;

    int thisSysVarsDegree = 0, thisGeneratedVarsDegree = 0, thisSysDegree = 0,
        thisGeneratedDegree = 0;
    bool canDivide = false;

    bool thisCleanIsolation = false;
    bool canReplace = true;

    int deg = degree(c->exp, v);
    ex lhs = expand(pow(v, deg));
    ex quoti = quo(c->exp, lhs, lhs);
    ex remain = expand(-rem(c->exp, lhs, lhs));
    DEBUG(5, "=========================\nLooking at variable: "
                 << v << " isolated as " << lhs << " * (" << quoti
                 << ") = " << remain << NL);

    if (degree(remain, v) != 0) {
      DEBUG(5, "Can't completely isolate " << v << " as it appears in "
                                           << remain << NL);
      continue;
    }

    SIGN qSign = tester->test(quoti).sign;
    DEBUG(5, "Variable " << v << " has coefficient " << quoti << " {" << qSign
                         << "}\n");
    switch (qSign) {
    case SIGN::ABSURD: {
      returnAbsurd();
      return false;
    }
    case SIGN::LEZ:
    case SIGN::GEZ:
    case SIGN::UNKNOWN: {
      DEBUG(5, "Can't use this variable for replacement\n");
      continue;
    }
    default:
      break;
    }

    ex rhs;
    bool thisCanDivide = divide(remain, quoti, rhs);
    bool negQuo = (qSign == SIGN::LTZ);
    if (!thisCanDivide) {
      if (negQuo) {
        DEBUG(5, quoti << " does not divide " << remain
                       << " and is negative, setting rhs = " << -remain
                       << ", and quoti = " << -quoti << NL);
        rhs = expand(-remain);
        quoti = expand(-quoti);
      } else {
        DEBUG(5, quoti << " does not divide " << remain
                       << ", setting rhs = " << remain << NL);
        rhs = remain;
      }
    } else {
      DEBUG(5, quoti << " divides " << remain << ", setting rhs =" << rhs
                     << " and quoti as 1\n");
      quoti = 1;
    }

    exset thisIneqs, thisEqs;
    Constraints thisToRemove;

    for (cc other : conju.ineqs) {
      int otherDegree = degree(other->exp, v);
      if (otherDegree == 0) {
        thisSysVarsDegree =
            max(thisSysVarsDegree, conju.varsDegree(other->exp));
        thisSysDegree = max(thisSysDegree, conju.polynomialDegree(other->exp));
        continue;
      }

      if ((deg != 1) and ((otherDegree % deg != 0) or
                          (degree(quo(other->exp, lhs, lhs), v) != 0))) {
        DEBUG(5, "Can't use " << lhs << " as it can't be properly isolated in "
                              << other << NL);
        canReplace = false;
        break;
      }
      DEBUG(5, "Replacing " << v << " = (" << rhs << ") / (" << quoti << ") on "
                            << other << NL);

      ex newcst = expand(
          subs(other->exp * power(quoti, otherDegree), v == (rhs / quoti)));
      bool ok = true;
      if (is_a<add>(newcst)) {
        for (const ex &e : newcst) {
          if (e.denom() != 1) {
            DEBUG(5, newcst << " is nok\n");
            ok = false;
            break;
          }
        }
      } else if (newcst.denom() != 1) {
        DEBUG(5, newcst << " is nok\n");
        ok = false;
      }
      if (not ok) {
        newcst = rem(other->exp, v, v);
        DEBUG(8, "newcst = " << newcst << NL);
        ex q = quo(other->exp, v, v);
        DEBUG(8, "q = " << q << NL);
        int deg = 1;
        while (rem(q, v, v) != 0) {
          newcst = newcst * quoti + rem(q, v, v) * power(rhs, deg++);
          DEBUG(8, "newcst = " << newcst << NL);
          q = quo(q, v, v);
          DEBUG(8, "q = " << q << NL);
        }
        newcst = expand(newcst);
      }

      thisGeneratedVarsDegree =
          max(thisGeneratedVarsDegree, conju.varsDegree(newcst));
      thisGeneratedDegree =
          max(thisGeneratedDegree, conju.polynomialDegree(newcst));
      thisSysVarsDegree = max(thisSysVarsDegree, thisGeneratedVarsDegree);
      thisSysDegree = max(thisSysDegree, thisGeneratedDegree);

      DEBUG(4, "Replacing " << v << " on " << other << " get " << newcst << GE
                            << "0\n");
      thisToRemove.insert(other);
      thisIneqs.insert(newcst);
    }
    for (cc other : conju.eqs) {
      if (c == other)
        continue;

      int otherDegree = degree(other->exp, v);
      if (otherDegree == 0) {
        thisSysVarsDegree =
            max(thisSysVarsDegree, conju.varsDegree(other->exp));
        thisSysDegree = max(thisSysDegree, conju.polynomialDegree(other->exp));
        continue;
      }

      if ((deg != 1) and ((otherDegree % deg != 0) or
                          (degree(quo(other->exp, lhs, lhs), v) != 0))) {
        DEBUG(5, "Can't use " << lhs << " as it can't be properly isolated in "
                              << other << NL);
        canReplace = false;
        break;
      }
      ex newcst = expand(
          subs(other->exp * power(quoti, otherDegree), v == (rhs / quoti)));
      assertM(newcst.degree(v) == 0,
              "After replacing we still have the replaced variable\n");
      bool ok = true;
      if (is_a<add>(newcst)) {
        for (const ex &e : newcst) {
          if (e.denom() != 1) {
            DEBUG(5, newcst << " is nok\n");
            ok = false;
            break;
          }
        }
      } else if (newcst.denom() != 1) {
        DEBUG(5, newcst << " is nok\n");
        ok = false;
      }
      if (not ok) {
        newcst = rem(other->exp, v, v);
        DEBUG(8, "newcst = " << newcst << NL);
        ex q = quo(other->exp, v, v);
        DEBUG(8, "q = " << q << NL);
        int deg = 1;
        while (rem(q, v, v) != 0) {
          newcst = newcst * quoti + rem(q, v, v) * power(rhs, deg++);
          DEBUG(8, "newcst = " << newcst << NL);
          q = quo(q, v, v);
          DEBUG(8, "q = " << q << NL);
        }
        newcst = expand(newcst);
      }

      thisGeneratedVarsDegree =
          max(thisGeneratedVarsDegree, conju.varsDegree(newcst));
      thisGeneratedDegree =
          max(thisGeneratedDegree, conju.polynomialDegree(newcst));
      thisSysVarsDegree = max(thisSysVarsDegree, thisGeneratedVarsDegree);
      thisSysDegree = max(thisSysDegree, thisGeneratedDegree);
      DEBUG(4, "Replacing " << v << " on " << other << " get " << newcst
                            << " = 0\n");
      thisToRemove.insert(other);
      thisEqs.insert(newcst);
    }

    DEBUG(5, "Testing if we should take this replacement as best option!\n");
    DEBUG(5,
          "Could we perform the replacement everywhere? " << canReplace << NL);
    if (!canReplace)
      continue;

    DEBUG(5, "The generated system has a degree in the variables"
                 << LE << sysVarsDegree << "? " << thisSysVarsDegree << NL);
    if (sysVarsDegree < thisSysVarsDegree)
      continue;

    if (sysVarsDegree == thisSysVarsDegree) {
      DEBUG(5, "The generated constraints have a degree in the variables"
                   << LE << generatedVarsDegree << "? "
                   << thisGeneratedVarsDegree << NL);
      if (generatedVarsDegree < thisGeneratedVarsDegree)
        continue;

      if (generatedVarsDegree == thisGeneratedVarsDegree) {
        DEBUG(5, "The generated system has a maximum degree"
                     << LE << sysDegree << "? " << thisSysDegree << NL);
        if (sysDegree < thisSysDegree)
          continue;

        if (sysDegree == thisSysDegree) {
          DEBUG(5, "The generated constraints have a maximum degree"
                       << LE << generatedDegree << "? " << thisGeneratedDegree
                       << NL);
          if (generatedDegree < thisGeneratedDegree)
            continue;

          if (generatedDegree == thisGeneratedDegree) {
            DEBUG(5, "When replacing the variable, did we perform a 'cleaner "
                     "isolation'? "
                         << (thisCleanIsolation > cleanIsolation) << NL);
            if (cleanIsolation > thisCleanIsolation)
              continue;

            if (cleanIsolation == thisCleanIsolation) {
              DEBUG(5,
                    "Did the quotient better divide the remaining expression? "
                        << ((not canDivide) and thisCanDivide) << NL);
              if ((not canDivide) and thisCanDivide)
                continue;
            }
          }
        }
      }
    }

    sysVarsDegree = thisSysVarsDegree;
    generatedVarsDegree = thisGeneratedVarsDegree;
    sysDegree = thisSysDegree;
    generatedDegree = thisGeneratedDegree;
    cleanIsolation = thisCleanIsolation;
    canDivide = thisCanDivide;
    eliminated = v;
    toRemove = std::move(thisToRemove);
    ineqs = std::move(thisIneqs);
    eqs = std::move(thisEqs);
    DEBUG(4,
          "Best replacement so far:\n\tReplacing: "
              << eliminated << "\nObtaining:\n\tSystem degree in variables:"
              << sysVarsDegree << "\n\tNew constraints max degree in variables:"
              << generatedVarsDegree << "\n\tSystem degree in variables:"
              << sysVarsDegree << "\n\tSystem degree:" << sysDegree
              << "\n\tGenerated constraints max degree: " << generatedDegree
              << "\n\tCould completely isolate the variable? " << cleanIsolation
              << "\n\tThe variable quotient did divide the remaining of the "
                 "equality ? "
              << canDivide << NL);
  }

  if (eliminated != 0) {
    toRemove.insert(c);
    Constraints toAdd;
    if ((conju.varsDegree(c->exp) == 0) or usePars) {
      DEBUG(4, "Replaced " << eliminated << " everywhere else, converting " << c
                           << " to 2 inequalities!\n");
      toAdd.insert(Constraint::get(c->exp));
      toAdd.insert(Constraint::get(-c->exp));
    } else {
      DEBUG(4, "==> Eliminated variable " << eliminated << NL);
    }
    for (const ex &e : ineqs)
      toAdd.insert(Constraint::get(e));
    for (const ex &e : eqs)
      toAdd.insert(Constraint::get(e, true));
    conju.removeJoin(toRemove, toAdd);
    conju.removeUnused();
    DEBUG(0, "Current system is: " << conju << NL);
    if (conju.hasEqs())
      gaussian_replacement(usePars);
    else {
      DEBUG(0, "System after gaussian_replacement:\n" << conju);
    }
    return true;
  } else if (!usePars) {
    return gaussian_replacement(true);
  }
  return false;
}

void Simplifier::Motzkin() {
  DEBUG(0, "Applying motzkin over:\n" << conju);
  if (targetDegree == 0)
    selectTarget();

  DEBUG(0, "Selecting variable " << target << ", with degree " << targetDegree
                                 << " for elimination");

  ex target_here = this->target;
  if (not(not_lifting or (targetDegree < min(2u, lifting_target_degree)))) {
    target_here = power(target, targetDegree);
    DEBUG(0, "Performing Motzkin by lifting " << target_here
                                              << " as the target variable");
  }

  Constraints remaining, zero, lb, ub;
  assert(conju.eqs.empty());
  gexmap<testResult> sign_cache;
  for (cc c : conju.ineqs) {
    unsigned deg = degree(c->exp, target_here);
    if (deg == 0) {
      DEBUG(6, c << " does not contains " << target_here << NL);
      remaining.insert(c);
      continue;
    }
    ex q = expand(quo(c->exp, target_here, target_here));

    testResult res;
    auto it = sign_cache.find(q);
    if (it != sign_cache.end()) {
      res = it->second;
      DEBUG(0, "We have cached that the sign of " << q << " is " << res << NL);
    } else {
      it = sign_cache.find(expand(-q));
      if (it != sign_cache.end()) {
        res = it->second;
        DEBUG(0, "We have cached that the sign of minus (" << q << ") is "
                                                           << res << NL);
        switch (res.sign) {
        case SIGN::GEZ:
          res.sign = SIGN::LEZ;
          break;
        case SIGN::GTZ:
          res.sign = SIGN::LTZ;
          break;
        case SIGN::LEZ:
          res.sign = SIGN::GEZ;
          break;
        case SIGN::LTZ:
          res.sign = SIGN::GTZ;
          break;
        default:
          break;
        }
      } else {
        res = tester->test(q);
        sign_cache[q] = res;
      }
    }

    DEBUG(0, c << " contains " << target_here << " with coefficient " << q
               << " which is of sign: " << res);
    switch (res.sign) {
    case SIGN::ABSURD: {
      DEBUG(0, "sign of " << q << " is an absurd\n";
            tester->printResult(cerr, true););
      returnAbsurd();
      return;
    }
    case SIGN::GTZ:
      DEBUG(3, "System has that " << q << " > 0\n")
      lb.insert(c);
      break;

    case SIGN::LTZ:
      ub.insert(c);
      DEBUG(3, "System has that " << q << " < 0\n")
      break;
    case SIGN::GEZ: {
      Conjunction ns = conju & Constraint::get(q - 1);
      conju.removeJoin({}, {Constraint::get(q, true)});
      DEBUG(2, q << " = " << res << NL << ns << NL << conju << NL);
#ifdef SCRIPT_CONTROL
      cout.flush();
      cout << ns << NL << conju << NL;
      clear();
      exit(0);
#else
      ret.push_back(ns);
      return;
#endif
    } break;
    case SIGN::UNKNOWN: {
      Conjunction ns = conju & Constraint::get(q - 1);
      Conjunction ns3 = conju & Constraint::get(-q - 1);
      conju.removeJoin({}, {Constraint::get(q, true)});
      DEBUG(2, q << " = " << res << NL << ns << NL << conju << NL << ns3 << NL);
#ifdef SCRIPT_CONTROL
      cout.flush();
      cout << ns << NL << conju << NL << ns3 << NL;
      clear();
      exit(0);
#else
      ret.push_back(ns);
      ret.push_back(ns3);
      return;
#endif
    } break;
    case SIGN::LEZ: {
      Conjunction ns2 = conju & Constraint::get(-q - 1);
      conju.removeJoin({}, {Constraint::get(q, true)});
      DEBUG(2, q << " = " << res << NL << ns2 << NL << conju << NL);
#ifdef SCRIPT_CONTROL
      cout.flush();
      cout << ns2 << NL << conju << NL;
      clear();
      exit(0);
#else
      ret.push_back(ns2);
      return;
#endif
    } break;
    case SIGN::ZERO:
      zero.insert(c);
      break;
    }
  }

  typedef map<unsigned, Constraints> cMap;
  cMap lowerBounds, upperBounds;
  for (cc c : lb) {
    unsigned deg = degree(c->exp, target_here);
    lowerBounds[deg - 1].insert(c);
  }

  for (cc c : ub) {
    unsigned deg = degree(c->exp, target_here);
    upperBounds[deg - 1].insert(c);
  }
  exset newConstraints;
  newConstraints.insert(1);
  unsigned newMaxDegree = 0;
  //  const ex powerRemoval = GiNaC::pow(2 * 3 * 5 * 7 * 9 * 11 * 13 * 17 * 19 *
  //  23, 4);
  for (cMap::const_iterator lbIt = lowerBounds.begin();
       lbIt != lowerBounds.end(); lbIt++) {
    for (cc lb : lbIt->second) {
      const ex loCoeff = quo(lb->exp, target_here, target_here);
      const ex loRemai = rem(lb->exp, target_here, target_here);
      for (cMap::const_iterator ubIt = upperBounds.begin();
           ubIt != upperBounds.end(); ubIt++) {
        for (cc ub : ubIt->second) {
          const ex upCoeff = quo(ub->exp, target_here, target_here);
          const ex upRemai = rem(ub->exp, target_here, target_here);
          ex newCstr = 0;
          newCstr = expand(loCoeff * upRemai - upCoeff * loRemai);
          newMaxDegree = std::max((unsigned)(abs(degree(newCstr, target_here))),
                                  newMaxDegree);
          DEBUG(3, "We have that:\n"
                       << "\tlower bound:" << lb
                       << " | written as: " << target_here << GE << '('
                       << expand(-loRemai) << ") / (" << loCoeff << ")\n"
                       << "\tupper bound:" << ub
                       << " | written as: " << target_here << LE << '('
                       << expand(-upRemai) << ") / (" << upCoeff << ")\n"
                       << "\tgiving: " << newCstr << GE << 0 << NL);
          if (is_a<numeric>(newCstr)) {
            if (newCstr < 0) {
              DEBUG(3, "Which is an absurd constraint, returning false!\n");
              _returnAbsurd();
              return;
            } else
              continue;
          }
          newConstraints.insert(newCstr);
        }
      }
    }
  }
  if (zero.size() > 0) {
    exset nc;
    Constraints nr;
    for (cc c : zero) {
      ex q = quo(c->exp, target_here, target_here);
      ex newCst =
          subs(subs(subs(c->exp, target_here == 0), q == 0), expand(-q) == 0);
      nr.insert(Constraint::get(newCst));
      nr.insert(Constraint::get(q));
      nr.insert(Constraint::get(-q));
      for (const ex &e : newConstraints)
        nc.insert(subs(subs(e, q == 0), expand(-q) == 0));

      for (cc e : remaining)
        nr.insert(
            Constraint::get((subs(subs(e->exp, q == 0), expand(-q) == 0))));

      swap(nc, newConstraints);
      swap(nr, remaining);
    }
  }
  if (newMaxDegree == 0) {
    for (const ex &constraint : newConstraints) {
      remaining.insert(Constraint::get(constraint));
    }

    Symbols vars;
    for (const ex &s : conju.vars)
      if (s != target_here)
        vars.append(s);

    DEBUG(6, "Variable " << target_here << " has been eliminated." << NL);
    targetDegree = 0;
    not_lifting = 2;
    lifting_target_degree = 999;
    conju = Conjunction(vars, conju.pars, conju.eqs, remaining, conju.id());
    DEBUG(4, conju << NL);
    return;
  }
  DEBUG(2, "New constraints have same target |"
               << target_here << "| at maximum degree of " << newMaxDegree
               << NL);
  lifting_target_degree = min(lifting_target_degree, targetDegree - 1);
  DEBUG(0, "Target is to lower " << target_here << " to the degree "
                                 << lifting_target_degree);

  if (not_lifting)
    not_lifting--;

  for (cMap::const_iterator it = lowerBounds.begin(); it != lowerBounds.end();
       it++) {
    if (it->first < max((unsigned)1, lifting_target_degree))
      remaining.insert(it->second.begin(), it->second.end());
  }

  for (cMap::const_iterator it = upperBounds.begin(); it != upperBounds.end();
       it++) {
    if (it->first < max((unsigned)1, lifting_target_degree))
      remaining.insert(it->second.begin(), it->second.end());
  }

  Constraints newSys = remaining;
  for (const ex &constraint : newConstraints) {
    newSys.insert(Constraint::get(constraint));
  }

  conju = Conjunction(conju.vars, conju.pars, conju.eqs, newSys, conju.id());
  if (lifting_target_degree > 1) {
    DEBUG(4, conju << NL);
    return;
  }
  conju.removeJoin({}, remaining);
  DEBUG(4, conju << NL);
}

void Simplifier::selectTarget() {
  ex variable;
  unsigned numExps = 99999, nonNum = 99999;
  unsigned degree = 99999;
  assert(conju.eqs.empty());
  for (const ex &s : conju.vars) {
    bool newVar = true;
    unsigned varDegree = 0, exps = 0, nonNumeric = 0;
    for (const cc c : conju.ineqs) {
      ex q = quo(c->exp, s, s);
      if (q.is_zero()) {
        continue;
      }
      exps++;
      unsigned dg = (unsigned)(abs(c->exp.degree(s)));
      for (const ex &e : conju.vars) {
        if (s == e)
          continue;

        dg += (unsigned)(abs(q.degree(e)));
      }
      varDegree = std::max(varDegree, dg);

      if (varDegree >= degree) {
        newVar = false;
        break;
      }

      if (not is_a<numeric>(q))
        nonNumeric++;

      if (varDegree == degree and (nonNumeric > nonNum)) {
        newVar = false;
        break;
      }
      if (varDegree == degree and (nonNumeric == nonNum) and
          (exps >= numExps)) {
        newVar = false;
        break;
      }
    }

    if (newVar) {
      variable = s;
      degree = varDegree;
      numExps = exps;
      nonNum = nonNumeric;
    }
  }
  target = variable;
  targetDegree = degree;
}
