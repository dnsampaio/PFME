#pragma once
#ifndef _DISJUNCTION_HPP_
#define _DISJUNCTION_HPP_
#include "Conjunction.hpp"
using namespace std;

typedef list<Conjunction> Conjs;
class Disjunction
{
  public:
    typedef Conjunction Conj;
    typedef Conjs::iterator iterator;
    typedef Conjs::const_iterator citerator;

    void join(const Conjs & cjs);
    void join(const Disjunction & other);
    void removeImplicators();
    Disjunction();
    Disjunction(istream &in);
    void read(istream &in);
    void simplifyFactor();

    void removeDuplicates();
    void eliminateVariables();

    size_t size() const{
      return conjs.size();
    }

    Conjs::const_iterator begin() const {
      return conjs.begin();
    }

    Conjs::const_iterator end() const {
      return conjs.end();
    }


    ostream &print(ostream &out) const;
    ostream &c_print(ostream &out) const;
  private:
    Conjs conjs;
};

ostream &operator<<(ostream &out, const Disjunction& s);
#endif
