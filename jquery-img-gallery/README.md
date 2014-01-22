jquery-img-gallery
==================
A basic sliding image gallery in JQuery with arrow-key and click navigation, delayed loading of secondary images, and a cute slider. Works decently well in mobile. Demo here: http://simoncharlow.com/diptychs

To use: modify the image src's and id's in `index.html` and the top two un-commented lines in `js.js`, then (minify and) save as `js.min.js`. You can also fiddle with transition timing (currently set to 400ms) and/or tweak the slider offset (currently set to 2px). 

The script dynamically (re)sizes important layout elements on load and window resize and ensures that the length of the transitions doesn't exceed the forced separation between multiple click/arrow events, on pain of funny things happening. 
