template <typename RETURN, class RECEIVER>
void gauge(RETURN (RECEIVER::*FUN)(void));

template <typename RETURN, class RECEIVER, typename ARG1>
void gauge(RETURN (RECEIVER::*)(ARG1));

template <typename RETURN, class RECEIVER, typename ARG1, typename ARG2>
void gauge(RETURN (RECEIVER::*)(ARG1, ARG2));

template <typename RETURN, class RECEIVER, typename ARG1, typename ARG2, typename ARG3>
struct gauge_member_fun
{
  typedef RETURN (*ref)(RECEIVER&, ARG1, ARG2, ARG3);

  template <RETURN (RECEIVER::*MEMBER_FUN)(ARG1, ARG2, ARG3)>
  struct regauge2
  {
    static RETURN ref(RECEIVER& r, ARG1 a1, ARG2 a2, ARG3 a3) { return (r.*MEMBER_FUN)(a1, a2, a3); }
  };

  template <RETURN (RECEIVER::*MEMBER_FUN)(ARG1, ARG2, ARG3)>
  ref regauge(void) const
  {
    return regauge2<MEMBER_FUN>::ref;
  }
};

template <typename RETURN, class RECEIVER, typename ARG1, typename ARG2, typename ARG3>
struct gauge_member_cfun
{
  typedef RETURN (*ref)(const RECEIVER&, ARG1, ARG2, ARG3);

  template <RETURN (RECEIVER::*MEMBER_FUN)(ARG1, ARG2, ARG3) const>
  struct regauge2
  {
    static RETURN ref(const RECEIVER& r, ARG1 a1, ARG2 a2, ARG3 a3) { return (r.*MEMBER_FUN)(a1, a2, a3); }
  };

  template <RETURN (RECEIVER::*MEMBER_FUN)(ARG1, ARG2, ARG3) const>
  ref regauge(void) const
  {
    return regauge2<MEMBER_FUN>::ref;
  }
};

template <typename RETURN, class RECEIVER, typename ARG1, typename ARG2, typename ARG3>
gauge_member_fun<RETURN, RECEIVER, ARG1, ARG2, ARG3> gauge(RETURN (RECEIVER::*)(ARG1, ARG2, ARG3));
template <typename RETURN, class RECEIVER, typename ARG1, typename ARG2, typename ARG3>
gauge_member_cfun<RETURN, RECEIVER, ARG1, ARG2, ARG3> gauge(RETURN (RECEIVER::*)(ARG1, ARG2, ARG3) const);


template <typename RETURN, typename ARG1, typename ARG2, typename ARG3>
void gauge(RETURN (*)(ARG1, ARG2, ARG3));

template <typename RETURN, class RECEIVER>
struct gauge_member
{
  typedef const RETURN& (*ref)(const RECEIVER&);

  template <RETURN RECEIVER::*MEMBER>
  struct regauge2
  {
    static const RETURN& ref(const RECEIVER& r) { return r.*MEMBER; }
  };

  template <RETURN RECEIVER::*MEMBER>
  ref regauge(void) const
  {
    return regauge2<MEMBER>::ref;
  }
};

template <typename RETURN, class RECEIVER>
gauge_member<RETURN, RECEIVER> gauge(RETURN RECEIVER::*member)
{
  return gauge_member<RETURN, RECEIVER>();
}

struct Foo
{
  int bla;
  void foo0();
  Foo& foo1(int*);
  void foo2(int*, Foo*);
  char* foo3(int, Foo&, const Foo*);
  char* foo3c(int, Foo&, const Foo*) const;
  static char* bar3(int, Foo&, const char*);
};

//namespace {
  void gaugers(void)
  {
    gauge(&Foo::foo0);
    gauge(&Foo::foo1);
    gauge(&Foo::foo2);
    gauge(&Foo::foo3).regauge<&Foo::foo3>();
    gauge(&Foo::foo3c).regauge<&Foo::foo3c>();
    gauge(&Foo::bar3);
    gauge(&Foo::bla).regauge<&Foo::bla>();
  }
//}
