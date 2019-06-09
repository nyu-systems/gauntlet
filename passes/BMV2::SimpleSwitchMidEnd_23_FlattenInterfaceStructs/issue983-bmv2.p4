--- before_pass
+++ after_pass
@@ -19,7 +19,16 @@ struct fwd_meta_t {
     bit<32> exp_x4;
 }
 struct metadata {
-    fwd_meta_t fwd_meta;
+    bit<16> _fwd_meta_tmp0;
+    bit<32> _fwd_meta_x11;
+    bit<16> _fwd_meta_x22;
+    bit<32> _fwd_meta_x33;
+    bit<32> _fwd_meta_x44;
+    bit<16> _fwd_meta_exp_etherType5;
+    bit<32> _fwd_meta_exp_x16;
+    bit<16> _fwd_meta_exp_x27;
+    bit<32> _fwd_meta_exp_x38;
+    bit<32> _fwd_meta_exp_x49;
 }
 struct headers {
     ethernet_t ethernet;
@@ -38,19 +47,19 @@ control ingress(inout headers hdr, inout
     }
     @name("ingress.debug_table_cksum1") table debug_table_cksum1_0 {
         key = {
-            hdr.ethernet.srcAddr            : exact @name("hdr.ethernet.srcAddr") ;
-            hdr.ethernet.dstAddr            : exact @name("hdr.ethernet.dstAddr") ;
-            hdr.ethernet.etherType          : exact @name("hdr.ethernet.etherType") ;
-            user_meta.fwd_meta.exp_etherType: exact @name("user_meta.fwd_meta.exp_etherType") ;
-            user_meta.fwd_meta.tmp          : exact @name("user_meta.fwd_meta.tmp") ;
-            user_meta.fwd_meta.exp_x1       : exact @name("user_meta.fwd_meta.exp_x1") ;
-            user_meta.fwd_meta.x1           : exact @name("user_meta.fwd_meta.x1") ;
-            user_meta.fwd_meta.exp_x2       : exact @name("user_meta.fwd_meta.exp_x2") ;
-            user_meta.fwd_meta.x2           : exact @name("user_meta.fwd_meta.x2") ;
-            user_meta.fwd_meta.exp_x3       : exact @name("user_meta.fwd_meta.exp_x3") ;
-            user_meta.fwd_meta.x3           : exact @name("user_meta.fwd_meta.x3") ;
-            user_meta.fwd_meta.exp_x4       : exact @name("user_meta.fwd_meta.exp_x4") ;
-            user_meta.fwd_meta.x4           : exact @name("user_meta.fwd_meta.x4") ;
+            hdr.ethernet.srcAddr              : exact @name("hdr.ethernet.srcAddr") ;
+            hdr.ethernet.dstAddr              : exact @name("hdr.ethernet.dstAddr") ;
+            hdr.ethernet.etherType            : exact @name("hdr.ethernet.etherType") ;
+            user_meta._fwd_meta_exp_etherType5: exact @name("user_meta.fwd_meta.exp_etherType") ;
+            user_meta._fwd_meta_tmp0          : exact @name("user_meta.fwd_meta.tmp") ;
+            user_meta._fwd_meta_exp_x16       : exact @name("user_meta.fwd_meta.exp_x1") ;
+            user_meta._fwd_meta_x11           : exact @name("user_meta.fwd_meta.x1") ;
+            user_meta._fwd_meta_exp_x27       : exact @name("user_meta.fwd_meta.exp_x2") ;
+            user_meta._fwd_meta_x22           : exact @name("user_meta.fwd_meta.x2") ;
+            user_meta._fwd_meta_exp_x38       : exact @name("user_meta.fwd_meta.exp_x3") ;
+            user_meta._fwd_meta_x33           : exact @name("user_meta.fwd_meta.x3") ;
+            user_meta._fwd_meta_exp_x49       : exact @name("user_meta.fwd_meta.exp_x4") ;
+            user_meta._fwd_meta_x44           : exact @name("user_meta.fwd_meta.x4") ;
         }
         actions = {
             NoAction_0();
@@ -61,26 +70,26 @@ control ingress(inout headers hdr, inout
         tmp_0 = ~hdr.ethernet.etherType;
         x1_0 = (bit<32>)tmp_0;
         x2_0 = x1_0[31:16] + x1_0[15:0];
-        user_meta.fwd_meta.tmp = tmp_0;
-        user_meta.fwd_meta.x1 = x1_0;
-        user_meta.fwd_meta.x2 = x2_0;
-        user_meta.fwd_meta.x3 = (bit<32>)~hdr.ethernet.etherType;
-        user_meta.fwd_meta.x4 = ~(bit<32>)hdr.ethernet.etherType;
-        user_meta.fwd_meta.exp_etherType = 16w0x800;
-        user_meta.fwd_meta.exp_x1 = 32w0xf7ff;
-        user_meta.fwd_meta.exp_x2 = 16w0xf7ff;
-        user_meta.fwd_meta.exp_x3 = 32w0xf7ff;
-        user_meta.fwd_meta.exp_x4 = 32w0xfffff7ff;
+        user_meta._fwd_meta_tmp0 = tmp_0;
+        user_meta._fwd_meta_x11 = x1_0;
+        user_meta._fwd_meta_x22 = x2_0;
+        user_meta._fwd_meta_x33 = (bit<32>)~hdr.ethernet.etherType;
+        user_meta._fwd_meta_x44 = ~(bit<32>)hdr.ethernet.etherType;
+        user_meta._fwd_meta_exp_etherType5 = 16w0x800;
+        user_meta._fwd_meta_exp_x16 = 32w0xf7ff;
+        user_meta._fwd_meta_exp_x27 = 16w0xf7ff;
+        user_meta._fwd_meta_exp_x38 = 32w0xf7ff;
+        user_meta._fwd_meta_exp_x49 = 32w0xfffff7ff;
         hdr.ethernet.dstAddr = 48w0;
-        if (hdr.ethernet.etherType != user_meta.fwd_meta.exp_etherType) 
+        if (hdr.ethernet.etherType != user_meta._fwd_meta_exp_etherType5) 
             hdr.ethernet.dstAddr[47:40] = 8w1;
-        if (user_meta.fwd_meta.x1 != user_meta.fwd_meta.exp_x1) 
+        if (user_meta._fwd_meta_x11 != user_meta._fwd_meta_exp_x16) 
             hdr.ethernet.dstAddr[39:32] = 8w1;
-        if (user_meta.fwd_meta.x2 != user_meta.fwd_meta.exp_x2) 
+        if (user_meta._fwd_meta_x22 != user_meta._fwd_meta_exp_x27) 
             hdr.ethernet.dstAddr[31:24] = 8w1;
-        if (user_meta.fwd_meta.x3 != user_meta.fwd_meta.exp_x3) 
+        if (user_meta._fwd_meta_x33 != user_meta._fwd_meta_exp_x38) 
             hdr.ethernet.dstAddr[23:16] = 8w1;
-        if (user_meta.fwd_meta.x4 != user_meta.fwd_meta.exp_x4) 
+        if (user_meta._fwd_meta_x44 != user_meta._fwd_meta_exp_x49) 
             hdr.ethernet.dstAddr[15:8] = 8w1;
         debug_table_cksum1_0.apply();
     }
