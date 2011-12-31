template <typename RETURN, class RECEIVER>
void gauge(RETURN (RECEIVER::*FUN)(void));

template <typename RETURN, class RECEIVER, typename ARG1>
void gauge(RETURN (RECEIVER::*)(ARG1));

template <typename RETURN, class RECEIVER, typename ARG1, typename ARG2>
void gauge(RETURN (RECEIVER::*)(ARG1, ARG2));

template <typename RETURN, class RECEIVER, typename ARG1, typename ARG2, typename ARG3>
struct gauge3
{
  template <RETURN (RECEIVER::*)(ARG1, ARG2, ARG3)>
  void regauge(void) const;
};

template <typename RETURN, class RECEIVER, typename ARG1, typename ARG2, typename ARG3>
gauge3<RETURN, RECEIVER, ARG1, ARG2, ARG3> gauge(RETURN (RECEIVER::*)(ARG1, ARG2, ARG3));


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
  static char* bar3(int, Foo&, const char*);
};

// template void gauge2<char*, Foo, int, Foo&, const Foo*, &Foo::foo3>(__typeof__(&Foo::foo3));

void gaugers(void)
{
  gauge(&Foo::foo0);
  gauge(&Foo::foo1);
  gauge(&Foo::foo2);
  gauge(&Foo::foo3);
  //  gauge2<char*, Foo, int, Foo&, &Foo::foo3>(&Foo::foo3);
  gauge(&Foo::foo3).regauge<&Foo::foo3>();
  gauge(&Foo::bar3);
  gauge(&Foo::bla).regauge<&Foo::bla>();
}
