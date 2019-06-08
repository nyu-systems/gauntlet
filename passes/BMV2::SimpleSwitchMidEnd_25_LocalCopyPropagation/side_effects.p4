--- dumps/pruned/side_effects-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-06-08 18:33:53.800861300 +0200
+++ dumps/pruned/side_effects-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-06-08 18:33:53.803406400 +0200
@@ -9,39 +9,32 @@ control my() {
     bit<1> a;
     H[2] s;
     bit<1> tmp_12;
-    bit<1> tmp_13;
     bit<1> tmp_14;
     bit<1> tmp_15;
-    bit<1> tmp_16;
     bit<1> tmp_17;
     bit<1> tmp_18;
-    bit<1> tmp_19;
     bit<1> tmp_20;
     bit<1> tmp_21;
     bit<1> tmp_22;
     bit<1> tmp_23;
-    bit<1> tmp_24;
     apply {
         a = 1w0;
         tmp_12 = g(a);
-        tmp_13 = tmp_12;
-        tmp_14 = f(a, tmp_13);
+        tmp_14 = f(a, tmp_12);
         a = tmp_14;
         tmp_15 = g(a);
-        tmp_16 = tmp_15;
-        tmp_17 = f(s[a].z, tmp_16);
+        tmp_17 = f(s[a].z, tmp_15);
         a = tmp_17;
         tmp_18 = g(a);
-        tmp_19 = tmp_18;
-        tmp_20 = s[tmp_19].z;
+        tmp_20 = s[tmp_18].z;
         tmp_21 = f(tmp_20, a);
-        s[tmp_19].z = tmp_20;
+        s[tmp_18].z = tmp_20;
         a = tmp_21;
         tmp_22 = g(a);
         a = tmp_22;
         tmp_23 = g(a[0:0]);
         a[0:0] = tmp_23;
-        tmp_24 = g(a);
+        g(a);
     }
 }
 top(my()) main;
