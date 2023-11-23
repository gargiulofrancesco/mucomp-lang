component EntryPoint provides App { 
  def main() : int {
  

    var n : int;
    n = 5;
    print(n++); 		//5
    print(++n); 		//7
    
    //testing references
    var ref : &int;
    ref = &n; 			//n=7
    print(ref++);		//7
    print(n);			//8 
    
    //testing arrays
    var arr : int[3];
    arr[0]=ref; 		//arr[0]=8
    print(arr[0]++);		//8
    print(++arr[0]);		//10
 
    //testing arrays of references
    var arr_ref : &int[3];
    arr_ref[0] = &arr[0]; 	//arr[0]=10
    print(arr_ref[0]++); 	//10
    print(arr[0]); 		//11
 

    
    return 0;
  }
}
