template <typename RETURN, class RECEIVER>
void gauge(RETURN (RECEIVER::*FUN)(void));

template <typename RETURN, class RECEIVER, typename ARG1>
void gauge(RETURN (RECEIVER::*)(ARG1));

template <typename RETURN, class RECEIVER, typename ARG1, typename ARG2>
void gauge(RETURN (RECEIVER::*)(ARG1, ARG2));

template <typename RETURN, class RECEIVER, typename ARG1, typename ARG2, typename ARG3>
struct gauge_member_fun
{
  typedef RETURN (*call)(RECEIVER&, ARG1, ARG2, ARG3);

  template <RETURN (RECEIVER::*MEMBER_FUN)(ARG1, ARG2, ARG3)>
  struct _ { static RETURN call(RECEIVER& r, ARG1 a1, ARG2 a2, ARG3 a3) { return (r.*MEMBER_FUN)(a1, a2, a3); } };

  template <RETURN (RECEIVER::*MEMBER_FUN)(ARG1, ARG2, ARG3)>
  call regauge(void) const { return _<MEMBER_FUN>::call; }
};

template <typename RETURN, class RECEIVER, typename ARG1, typename ARG2, typename ARG3>
struct gauge_member_cfun
{
  typedef RETURN (*call)(const RECEIVER&, ARG1, ARG2, ARG3);

  template <RETURN (RECEIVER::*MEMBER_FUN)(ARG1, ARG2, ARG3) const>
  struct _ { static RETURN call(const RECEIVER& r, ARG1 a1, ARG2 a2, ARG3 a3) { return (r.*MEMBER_FUN)(a1, a2, a3); } };

  template <RETURN (RECEIVER::*MEMBER_FUN)(ARG1, ARG2, ARG3) const>
  call regauge(void) const { return _<MEMBER_FUN>::call; }
};

template <typename RETURN, class RECEIVER, typename ARG1, typename ARG2, typename ARG3>
gauge_member_fun<RETURN, RECEIVER, ARG1, ARG2, ARG3> gauge(RETURN (RECEIVER::*)(ARG1, ARG2, ARG3))
{ return gauge_member_fun<RETURN, RECEIVER, ARG1, ARG2, ARG3>(); }

template <typename RETURN, class RECEIVER, typename ARG1, typename ARG2, typename ARG3>
gauge_member_cfun<RETURN, RECEIVER, ARG1, ARG2, ARG3> gauge(RETURN (RECEIVER::*)(ARG1, ARG2, ARG3) const)
{ return gauge_member_cfun<RETURN, RECEIVER, ARG1, ARG2, ARG3>(); }


template <typename RETURN, typename ARG1, typename ARG2, typename ARG3>
void gauge(RETURN (*)(ARG1, ARG2, ARG3));

template <typename RETURN, class RECEIVER>
struct gauge_data_member
{
  typedef RETURN& (*ref)(RECEIVER&);

  template <RETURN RECEIVER::*MEMBER>
  struct _ { static RETURN& ref(RECEIVER& r) { return r.*MEMBER; } };

  template <RETURN RECEIVER::*MEMBER>
  ref regauge(void) const { return _<MEMBER>::ref; }
};

template <typename RETURN, class RECEIVER>
gauge_data_member<RETURN, RECEIVER> gauge(RETURN RECEIVER::*member)
{
  return gauge_data_member<RETURN, RECEIVER>();
}

struct Foo
{
  int bla;
  /* void foo0();
  Foo& foo1(int*);
  void foo2(int*, Foo*);*/
  char* foo3(int, Foo&, const Foo*);
  virtual const char* foo3c(int, char, unsigned) const;
  //static char* bar3(int, Foo&, const char*);
};

char* Foo::foo3(int, Foo&, const Foo*)
{
  return 0;
}

const char* Foo::foo3c(int, char, unsigned) const
{
  return "Hello gauge!";
}

//namespace {
  void gaugers(void)
  {
    /*    gauge(&Foo::foo0);
    gauge(&Foo::foo1);
    gauge(&Foo::foo2);*/
    gauge(&Foo::foo3).regauge<&Foo::foo3>();
    gauge(&Foo::foo3c).regauge<&Foo::foo3c>();
    //    gauge(&Foo::bar3);
    gauge(&Foo::bla).regauge<&Foo::bla>();
  }
//}

extern "C" char* _ZN17gauge_member_cfunIPKc3FooicjE1_IXadL_ZNKS2_5foo3cEicjEEE4callERKS2_icj(const Foo*, int, char, unsigned);

#include <cstdio>
int main(void)
{
  Foo foo;
  printf("%s\n", _ZN17gauge_member_cfunIPKc3FooicjE1_IXadL_ZNKS2_5foo3cEicjEEE4callERKS2_icj(&foo, 1, 2, 3));
}


