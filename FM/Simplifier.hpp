// Created on: Oct 11, 2015
// Author: Diogo N. SAMPAIO <dnsampaio@gmail.com>
//
//===-- /Simplifier/Motzkin.hpp - {Description} -------*- C++ -*-===//
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
#pragma once
#ifndef SIMPLIFIER_HPP_
#define SIMPLIFIER_HPP_

//#include "Constraint.hpp"
#include "Schweighofer.hpp"
#include "Disjunction.hpp"

//class Conjunction;

/* The simplifier class holds methods to apply Fourier-Motzkin to a set of constraints,
 * and remove rounding errors of relaxed constraints.*/
class Simplifier
{
  public:
    Simplifier(Conjunction &sys);
    ~Simplifier();
    Conjs get(){
      return ret;
    }
    void run();

    bool add_affine_planes();
    bool tightening();
    void split_space(const exset &pars);
    void Motzkin();
    bool getRoots();
    bool normalize();
    bool gaussian_replacement(){
          return gaussian_replacement(false) | gaussian_replacement(true);
    }
    bool gaussian_replacement(bool usePars);
    void clear();
    bool eqs_pattern_matching();
    bool eqs_affinize();
  private:
    struct relat{
      ex evidence;
      ex quo;
      ex rhs;
    };
    ex target;
    unsigned targetDegree = 0;
    void build_tester();
    ex   compose(const testResult tr, const ex &tested);
    bool proved(const testResult tr) const;
//    bool precision_increase();
    void selectTarget();
    int not_lifting = 2;
    unsigned lifting_target_degree = 999;

    relat put_in_evidence(ex exp, const exset &vars) const;
//    relat factorize(ex exp) const;
    inline void _returnAbsurd(){
#ifdef SCRIPT_CONTROL
      cout.flush();
      cerr.flush();
      cout << Conjunction::absurd << NL;
      clear();
      exit(0);
#else
      conju = Conjunction::absurd;
      ret.push_back(Conjunction::absurd);
#endif
    };

    Conjunction conju;
    Conjs ret;
    SchweighoferTester *tester = nullptr;
};

#endif /* SIMPLIFIER_HPP_ */
