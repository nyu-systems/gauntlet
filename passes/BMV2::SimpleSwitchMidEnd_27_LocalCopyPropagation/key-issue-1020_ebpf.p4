--- before_pass
+++ after_pass
@@ -39,7 +39,6 @@ parser prs(packet_in p, out Headers_t he
     }
 }
 control pipe(inout Headers_t headers, out bool pass) {
-    bool tmp;
     bit<32> key_0;
     bit<32> key_1;
     @name("pipe.invalidate") action invalidate() {
@@ -68,7 +67,7 @@ control pipe(inout Headers_t headers, ou
         {
             key_0 = headers.ipv4.srcAddr + 32w1;
             key_1 = headers.ipv4.dstAddr + 32w1;
-            tmp = t_0.apply().hit;
+            t_0.apply();
         }
     }
 }
