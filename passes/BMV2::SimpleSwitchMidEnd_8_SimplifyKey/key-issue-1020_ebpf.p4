--- dumps/pruned/key-issue-1020_ebpf-BMV2::SimpleSwitchMidEnd_7_TypeChecking.p4	2019-06-08 18:32:53.926545700 +0200
+++ dumps/pruned/key-issue-1020_ebpf-BMV2::SimpleSwitchMidEnd_8_SimplifyKey.p4	2019-06-08 18:32:53.929101100 +0200
@@ -48,12 +48,14 @@ control pipe(inout Headers_t headers, ou
     @name("pipe.drop") action drop_0() {
         pass = false;
     }
+    bit<32> key_0;
+    bit<32> key_1;
     @name("pipe.t") table t {
         key = {
-            headers.ipv4.srcAddr + 32w1: exact @name(" headers.ipv4.srcAddr") ;
-            headers.ipv4.dstAddr + 32w1: exact @name("headers.ipv4.dstAddr") ;
-            headers.ethernet.dstAddr   : exact @name("headers.ethernet.dstAddr") ;
-            headers.ethernet.srcAddr   : exact @name("headers.ethernet.srcAddr") ;
+            key_0                   : exact @name(" headers.ipv4.srcAddr") ;
+            key_1                   : exact @name("headers.ipv4.dstAddr") ;
+            headers.ethernet.dstAddr: exact @name("headers.ethernet.dstAddr") ;
+            headers.ethernet.srcAddr: exact @name("headers.ethernet.srcAddr") ;
         }
         actions = {
             invalidate_0();
@@ -63,7 +65,11 @@ control pipe(inout Headers_t headers, ou
         default_action = drop_0();
     }
     apply {
-        tmp_0 = t.apply().hit;
+        {
+            key_0 = headers.ipv4.srcAddr + 32w1;
+            key_1 = headers.ipv4.dstAddr + 32w1;
+            tmp_0 = t.apply().hit;
+        }
     }
 }
 ebpfFilter<Headers_t>(prs(), pipe()) main;
