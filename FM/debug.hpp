#ifndef _DEBUG_HPP__
#define _DEBUG_HPP__
#define __FILENAME__ (strrchr(__FILE__, '/') ? strrchr(__FILE__, '/') + 1 : __FILE__)
#include <iostream>
#include <string>
#include <cassert>

const std::string GE = u8" ≥ ";
const std::string LE = u8" ≤ ";
const std::string ALIKE = u8" ≈ ";
const std::string NE = u8" ≠ ";
const std::string PM = u8"±";
using namespace std;

#ifndef NL
#define NL std::endl
#endif
typedef struct{
    string DEB_FILE, DEB_FUNC;
} DEB_INF;
extern DEB_INF DI;
#define assertM(X, M){if(!(X)){cerr << __FILENAME__ << "::" << __func__ << "::" << __LINE__ << "Error: " << M << NL; assert(false);}};
#define messageM(X)cerr << __FILENAME__ << "::" << __func__ << "::" << __LINE__ << "::" << X << NL
bool getResponse(const string question, const bool def = true);
#endif

#ifndef DEB_LVL
#define DEB_LVL (-1)
#endif

#ifdef DEBUG
#undef DEBUG
#undef CLEAR_DEBUG
#endif

#ifdef NDEBUG
#define DEBUG(X, S){}
#define DEBUGFOR(C, X, S){}
#define DEBUGIF(X, S) if(false)
#else
#ifndef DEB_LVL
#define DEBUG(X, S){}
#define DEBUGFOR(C, X, S){}
#define DEBUGIF(X, S) if(false)
#else
#if DEB_LVL < 1
#define DEBUG(X, S){}
#define DEBUGFOR(C, X, S){}
#define DEBUGIF(X, S) if(false)
#else
#define DEBUG(X, S){\
if(X < DEB_LVL){\
  if((DI.DEB_FILE != __FILE__)||(DI.DEB_FUNC != __func__)){\
    DI.DEB_FILE = __FILE__;\
    DI.DEB_FUNC = __func__;\
    cerr << "================== " << __FILENAME__ << "::" << __func__ << " ==================" << NL;\
  }\
  cerr << __LINE__ << "::" << S;\
}}
#define DEBUGFOR(X, C, S){\
    if(X < DEB_LVL){\
      if((DI.DEB_FILE != __FILE__)||(DI.DEB_FUNC != __func__)){\
        DI.DEB_FILE = __FILE__;\
        DI.DEB_FUNC = __func__;\
        cerr << "================== " << __FILENAME__ << "::" << __func__ << " ==================" << NL;\
      }\
      for(C){\
        cerr << __LINE__ << "::" << S;\
    }}}
#define DEBUGIF(X, S) DEBUG(X, S) if(X < DEB_LVL)

#endif
#endif
#endif

#ifdef INTERACTIVE_MODE
#define IP(X){\
      if((DI.DEB_FILE != __FILE__)||(DI.DEB_FUNC != __func__)){\
        DI.DEB_FILE = __FILE__;\
        DI.DEB_FUNC = __func__;\
        cerr << "================== " << __FILENAME__ << "::" << __func__ << " ==================" << endl;\
      }\
      cerr << __LINE__ << "::" << X;\
    }
#else
#define IP(X){}
#endif
