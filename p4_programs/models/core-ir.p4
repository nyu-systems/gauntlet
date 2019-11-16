/* 
<P4Program>(140)
  <Type_Error>(15)
    <Declaration_ID>(7)
    <Declaration_ID>(8)
    <Declaration_ID>(9)
    <Declaration_ID>(10)
    <Declaration_ID>(11)
    <Declaration_ID>(12)
    <Declaration_ID>(13)
  <Type_Extern>(86)
    <TypeParameters>(17)
    <Method>(33)
      <Type_Method>(32)
        <TypeParameters>(23)
          <Type_Var>(21)
        <Type_Void>(0)
        <ParameterList>(30)
          <Parameter>(27)
      <Annotations>(3)
    <Method>(50)
      <Type_Method>(49)
        <TypeParameters>(37)
          <Type_Var>(35)
        <Type_Void>(0)
        <ParameterList>(47)
          <Parameter>(41)
          <Parameter>(45)
      <Annotations>(3)
    <Method>(63)
      <Type_Method>(62)
        <TypeParameters>(56)
          <Type_Var>(54)
        <Type_Name>(52)
          T
        <ParameterList>(60)
      <Annotations>(3)
    <Method>(74)
      <Type_Method>(73)
        <TypeParameters>(64)
        <Type_Void>(0)
        <ParameterList>(71)
          <Parameter>(68)
      <Annotations>(3)
    <Method>(84)
      <Type_Method>(83)
        <TypeParameters>(77)
        <Type_Bits>(1)
        <ParameterList>(81)
      <Annotations>(3)
    <Annotations>(3)
  <Type_Extern>(107)
    <TypeParameters>(89)
    <Method>(105)
      <Type_Method>(104)
        <TypeParameters>(95)
          <Type_Var>(93)
        <Type_Void>(0)
        <ParameterList>(102)
          <Parameter>(99)
      <Annotations>(3)
    <Annotations>(3)
  <Method>(122)
  <P4Action>(131)
  <Declaration_MatchKind>(137) */
/* 
  <Type_Error>(15)
    <Declaration_ID>(7)
    <Declaration_ID>(8)
    <Declaration_ID>(9)
    <Declaration_ID>(10)
    <Declaration_ID>(11)
    <Declaration_ID>(12)
    <Declaration_ID>(13) */
error {
/* 
    <Declaration_ID>(7) */
        NoError,
/* 
    <Declaration_ID>(8) */
        PacketTooShort,
/* 
    <Declaration_ID>(9) */
        NoMatch,
/* 
    <Declaration_ID>(10) */
        StackOutOfBounds,
/* 
    <Declaration_ID>(11) */
        HeaderTooShort,
/* 
    <Declaration_ID>(12) */
        ParserTimeout,
/* 
    <Declaration_ID>(13) */
        ParserInvalidArgument
}

/* 
  <Type_Extern>(86)
    <TypeParameters>(17)
    <Method>(33)
      <Type_Method>(32)
        <TypeParameters>(23)
          <Type_Var>(21)
        <Type_Void>(0)
        <ParameterList>(30)
          <Parameter>(27)
            <Annotations>(3)
            <Type_Name>(26)
              T
      <Annotations>(3)
    <Method>(50)
      <Type_Method>(49)
        <TypeParameters>(37)
          <Type_Var>(35)
        <Type_Void>(0)
        <ParameterList>(47)
          <Parameter>(41)
            <Annotations>(3)
            <Type_Name>(40)
              T
          <Parameter>(45)
            <Annotations>(3)
            <Type_Bits>(1)
      <Annotations>(3)
    <Method>(63)
      <Type_Method>(62)
        <TypeParameters>(56)
          <Type_Var>(54)
        <Type_Name>(52)
          T
        <ParameterList>(60)
      <Annotations>(3)
    <Method>(74)
      <Type_Method>(73)
        <TypeParameters>(64)
        <Type_Void>(0)
        <ParameterList>(71)
          <Parameter>(68)
            <Annotations>(3)
            <Type_Bits>(1)
      <Annotations>(3)
    <Method>(84)
      <Type_Method>(83)
        <TypeParameters>(77)
        <Type_Bits>(1)
        <ParameterList>(81)
      <Annotations>(3)
    <Annotations>(3) */
extern packet_in {
    /* 
    <Method>(33) */
    void extract<T>(/* 
        <Parameter>(27)
          <Annotations>(3)
          <Type_Name>(26)
            T */
out T hdr);
    /* 
    <Method>(50) */
    void extract<T>(/* 
        <Parameter>(41)
          <Annotations>(3)
          <Type_Name>(40)
            T */
out T variableSizeHeader, /* 
        <Parameter>(45)
          <Annotations>(3)
          <Type_Bits>(1) */
    in bit<32> variableFieldSizeInBits);
    /* 
    <Method>(63) */
    T lookahead<T>();
    /* 
    <Method>(74) */
    void advance(/* 
        <Parameter>(68)
          <Annotations>(3)
          <Type_Bits>(1) */
in bit<32> sizeInBits);
    /* 
    <Method>(84) */
    bit<32> length();
}

/* 
  <Type_Extern>(107)
    <TypeParameters>(89)
    <Method>(105)
      <Type_Method>(104)
        <TypeParameters>(95)
          <Type_Var>(93)
        <Type_Void>(0)
        <ParameterList>(102)
          <Parameter>(99)
            <Annotations>(3)
            <Type_Name>(98)
              T
      <Annotations>(3)
    <Annotations>(3) */
extern packet_out {
    /* 
    <Method>(105) */
    void emit<T>(/* 
        <Parameter>(99)
          <Annotations>(3)
          <Type_Name>(98)
            T */
in T hdr);
}

/* 
  <Method>(122) */
extern void verify(/* 
      <Parameter>(113)
        <Annotations>(3)
        <Type_Boolean>(112) */
in bool check, /* 
      <Parameter>(117)
        <Annotations>(3)
        <Type_Name>(116)
          error */
in error toSignal);
/* 
  <P4Action>(131)
    <Annotations>(3)
    <ParameterList>(129)
    <BlockStatement>(126) */
action NoAction() /* 
    <BlockStatement>(126) */
{
}
/* 
  <Declaration_MatchKind>(137) */
match_kind {
/* 
    <Declaration_ID>(133) */
        exact,
/* 
    <Declaration_ID>(134) */
        ternary,
/* 
    <Declaration_ID>(135) */
        lpm
}

