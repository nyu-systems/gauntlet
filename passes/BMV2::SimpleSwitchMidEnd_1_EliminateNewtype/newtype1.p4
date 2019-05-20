--- dumps/p4_16_samples/newtype1.p4/pruned/newtype1-BMV2::SimpleSwitchMidEnd_0_CheckTableSize.p4	2019-05-20 17:31:27.328747000 +0200
+++ dumps/p4_16_samples/newtype1.p4/pruned/newtype1-BMV2::SimpleSwitchMidEnd_1_EliminateNewtype.p4	2019-05-20 17:31:27.355680800 +0200
@@ -1,14 +1,14 @@
 typedef bit<9> Narrow_t;
-type Narrow_t Narrow;
+typedef Narrow_t Narrow;
 typedef bit<32> Wide_t;
-type Wide_t Wide;
+typedef Wide_t Wide;
 control c(out bool b) {
     Wide x;
     Narrow y;
     apply {
-        x = (Wide)32w3;
-        y = (Narrow)(Narrow_t)(Wide_t)x;
-        b = y == (Narrow)9w10;
+        x = 32w3;
+        y = (Narrow_t)(Wide_t)x;
+        b = y == 9w10;
     }
 }
 control ctrl(out bool b);
