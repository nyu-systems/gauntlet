--- dumps/pruned/ternary2-bmv2-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-06-08 18:34:16.797349000 +0200
+++ dumps/pruned/ternary2-bmv2-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-06-08 18:34:16.817791600 +0200
@@ -54,17 +54,25 @@ control ingress(inout packet_t hdrs, ino
     }
     @name("ingress.noop") action noop_8() {
     }
-    @name("ingress.setbyte") action setbyte_0(out bit<8> reg, bit<8> val) {
+    bit<8> reg;
+    @name("ingress.setbyte") action setbyte_0(bit<8> val) {
         reg = val;
+        hdrs.extra[0].b1 = reg;
     }
-    @name("ingress.setbyte") action setbyte_4(out bit<8> reg_1, bit<8> val) {
+    bit<8> reg_1;
+    @name("ingress.setbyte") action setbyte_4(bit<8> val) {
         reg_1 = val;
+        hdrs.data.b2 = reg_1;
     }
-    @name("ingress.setbyte") action setbyte_5(out bit<8> reg_2, bit<8> val) {
+    bit<8> reg_2;
+    @name("ingress.setbyte") action setbyte_5(bit<8> val) {
         reg_2 = val;
+        hdrs.extra[1].b1 = reg_2;
     }
-    @name("ingress.setbyte") action setbyte_6(out bit<8> reg_3, bit<8> val) {
+    bit<8> reg_3;
+    @name("ingress.setbyte") action setbyte_6(bit<8> val) {
         reg_3 = val;
+        hdrs.extra[2].b2 = reg_3;
     }
     @name("ingress.act1") action act1_0(bit<8> val) {
         hdrs.extra[0].b1 = val;
@@ -90,7 +98,7 @@ control ingress(inout packet_t hdrs, ino
             hdrs.extra[0].h: ternary @name("hdrs.extra[0].h") ;
         }
         actions = {
-            setbyte_0(hdrs.extra[0].b1);
+            setbyte_0();
             act1_0();
             act2_0();
             act3_0();
@@ -103,7 +111,7 @@ control ingress(inout packet_t hdrs, ino
             hdrs.data.f2: ternary @name("hdrs.data.f2") ;
         }
         actions = {
-            setbyte_4(hdrs.data.b2);
+            setbyte_4();
             noop_6();
         }
         default_action = noop_6();
@@ -113,7 +121,7 @@ control ingress(inout packet_t hdrs, ino
             hdrs.data.f2: ternary @name("hdrs.data.f2") ;
         }
         actions = {
-            setbyte_5(hdrs.extra[1].b1);
+            setbyte_5();
             noop_7();
         }
         default_action = noop_7();
@@ -123,7 +131,7 @@ control ingress(inout packet_t hdrs, ino
             hdrs.data.f2: ternary @name("hdrs.data.f2") ;
         }
         actions = {
-            setbyte_6(hdrs.extra[2].b2);
+            setbyte_6();
             noop_8();
         }
         default_action = noop_8();
