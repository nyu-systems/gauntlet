--- before_pass
+++ after_pass
@@ -40,11 +40,6 @@ control update(inout packet_t h, inout M
     }
 }
 control ingress(inout packet_t hdrs, inout Meta m, inout standard_metadata_t meta) {
-    bit<8> reg;
-    bit<8> reg_1;
-    bit<8> reg_2;
-    bit<8> reg_3;
-    bit<16> key_0;
     @name("ingress.setb1") action setb1_0(bit<9> port, bit<8> val) {
         hdrs.data.b1 = val;
         meta.egress_spec = port;
@@ -60,20 +55,16 @@ control ingress(inout packet_t hdrs, ino
     @name("ingress.noop") action noop_8() {
     }
     @name("ingress.setbyte") action setbyte_0(bit<8> val) {
-        reg = val;
-        hdrs.extra[0].b1 = reg;
+        hdrs.extra[0].b1 = val;
     }
     @name("ingress.setbyte") action setbyte_4(bit<8> val) {
-        reg_1 = val;
-        hdrs.data.b2 = reg_1;
+        hdrs.data.b2 = val;
     }
     @name("ingress.setbyte") action setbyte_5(bit<8> val) {
-        reg_2 = val;
-        hdrs.extra[1].b1 = reg_2;
+        hdrs.extra[1].b1 = val;
     }
     @name("ingress.setbyte") action setbyte_6(bit<8> val) {
-        reg_3 = val;
-        hdrs.extra[2].b2 = reg_3;
+        hdrs.extra[2].b2 = val;
     }
     @name("ingress.act1") action act1_0(bit<8> val) {
         hdrs.extra[0].b1 = val;
@@ -96,7 +87,7 @@ control ingress(inout packet_t hdrs, ino
     }
     @name("ingress.ex1") table ex1 {
         key = {
-            key_0: ternary @name("hdrs.extra[0].h") ;
+            hdrs.extra[0].h: ternary @name("hdrs.extra[0].h") ;
         }
         actions = {
             setbyte_0();
@@ -140,7 +131,6 @@ control ingress(inout packet_t hdrs, ino
     apply {
         test1.apply();
         {
-            key_0 = hdrs.extra[0].h;
             switch (ex1.apply().action_run) {
                 act1_0: {
                     tbl1.apply();
