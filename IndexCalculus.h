#ifndef _INDEXCALCULUS_H_
#define _INDEXCALCULUS_H_

#include <iostream>

#include <NTL/ZZ.h>
#include <NTL/ZZ_p.h>
#include <NTL/vec_long.h>
#include <NTL/vec_ZZ.h>

#include "smat_long.h"

#include "DLog_IC_Base.h"
#include "FactorBase.h"


NTL_OPEN_NNS;

/* The classic Index Calculus method for computing discrete logarithms.
 */
class IndexCalculus : public DLog_IC_Base {
public:
  // tuning parameters (these are evaluated with L_p()
  static double L_UB;    /* upper bound */

protected:
  // largest factor of group order
  ZZ q;

  // length of sieve
  long sieve_length;

  // factorbase
  FactorBase zfb;

  // "upper" factorbase
  vec_ZZ ufb;
  ZZ sufb;   // start of upper fb

public:
  IndexCalculus() : DLog_IC_Base() {
  }
  IndexCalculus(const ZZ_p& base, long bound=0, long length=0) 
    : DLog_IC_Base(base) {
    setBase(base,bound,length);
  }

  ~IndexCalculus() {
  }

  // set the base to use for logs and factorbase bound
  void setBase(const ZZ_p& base, long bound, long sieve_length=0);

  // set the base to use for logs
  // factorbase bound is determined automatically
  void setBase(const ZZ_p& base) {
    // the other setBase() will figure out the optimal parameters
    setBase(base,0);
  }

  // compute optimum parameters for a given p
  // either of bound or width that are non-zero are not computed
  static void parameters(long& bound, long& length, const ZZ& p);


private:
  // make the system of equations to solve the factorbase
  bool make_system();

  // solve A*x=b (mod q)
  bool solve_system(const smat_long& A, vec_ZZ& x, const vec_long& b, 
		    const ZZ& q);

  // find log (to base g) of a prime
  virtual ZZ log_prime(const ZZ& prime);

  // L_p[1/2;c] = exp(c*sqrt(log(p)*log(log(p))))
  inline static double L_p(const ZZ& p, double c) {
    double lm = NTL::log(p);
    double llm = ::log(lm);
    return exp(c*sqrt(lm*llm));
  }
};

NTL_CLOSE_NNS;

#endif
