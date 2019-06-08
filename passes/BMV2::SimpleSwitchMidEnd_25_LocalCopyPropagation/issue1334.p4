--- dumps/pruned/issue1334-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-06-08 18:31:59.186105300 +0200
+++ dumps/pruned/issue1334-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-06-08 18:31:59.188074800 +0200
@@ -10,7 +10,6 @@ extern Overloaded {
     void f(bit<32> a, bit<16> b);
 }
 control c() {
-    bit<32> z;
     @name("c.o") Overloaded() o;
     apply {
         f();
@@ -23,7 +22,6 @@ control c() {
         o.f(b = 16w1);
         o.f(a = 32w1, b = 16w2);
         o.f(a = 32w1, b = 16w2);
-        z = 32w4294967294;
     }
 }
 control proto();
