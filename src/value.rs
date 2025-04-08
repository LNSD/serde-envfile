cfg_if::cfg_if! {
    if #[cfg(feature = "preserve_order")] {
        use indexmap::map::{
            IndexMap as Map,
            IntoIter as InnerIntoIter,
            Iter as InnerIter,
            IterMut as InnerIterMut,
            Keys as InnerKeys,
            Values as InnerValues,
            ValuesMut as InnerValuesMut,
        };
    } else {
        // std::collections::HashMap vs hashbrown::HashMap
        // https://users.rust-lang.org/t/hashmap-and-hashbrown/114535/2
        use std::collections::hash_map::{
            HashMap as Map,
            IntoIter as InnerIntoIter,
            Iter as InnerIter,
            IterMut as InnerIterMut,
            Keys as InnerKeys,
            Values as InnerValues,
            ValuesMut as InnerValuesMut,
        };
    }
}

/// Flexible representation of environment variables.
///
/// # Example
///
/// ```rust
/// use serde_envfile::{Value, from_str};
///
/// // Create a simple envfile string
/// let envfile = "KEY1=\"VALUE1\"\nKEY2=\"VALUE2\"";
///
/// // Parse the envfile into a Value
/// let value: Value = from_str(envfile).expect("Failed to parse envfile");
/// # assert_eq!(value.get("key1").unwrap(), "VALUE1");
/// # assert_eq!(value.get("key2").unwrap(), "VALUE2");
///
/// // Iterate over the key-value pairs
/// for (key, value) in &value {
///     println!("{} = {}", key, value);
/// }
/// ```
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(transparent)]
pub struct Value(Map<String, String>);

impl Default for Value {
    fn default() -> Self {
        Self::new()
    }
}

impl Value {
    /// Create an empty [`Value`].
    ///
    /// A new empty environment variable map is created.
    pub fn new() -> Self {
        Self(Default::default())
    }

    /// Inserts a key-value pair into the environment variables.
    ///
    /// If the key already exists, the previous value is returned.
    ///
    /// # Example
    ///
    /// ```rust
    /// use serde_envfile::Value;
    ///
    /// let mut env = Value::new();
    ///
    /// // Insert a new key-value pair
    /// assert_eq!(env.insert("KEY1", "VALUE1"), None);
    ///
    /// // Insert with an existing key returns the previous value
    /// assert_eq!(env.insert("KEY1", "NEW_VALUE"), Some("VALUE1".to_string()));
    ///
    /// // The value was updated
    /// assert_eq!(env.get("KEY1").unwrap(), "NEW_VALUE");
    /// ```
    pub fn insert<K, V>(&mut self, key: K, value: V) -> Option<String>
    where
        K: Into<String>,
        V: Into<String>,
    {
        self.0.insert(key.into(), value.into())
    }

    /// Removes a key from the environment variables.
    ///
    /// Returns the value associated with the key if it was present.
    ///
    /// # Example
    ///
    /// ```rust
    /// use serde_envfile::Value;
    ///
    /// let mut env = Value::from_iter([("KEY1", "VALUE1"), ("KEY2", "VALUE2")]);
    ///
    /// // Remove an existing key
    /// assert_eq!(env.remove("KEY1"), Some("VALUE1".to_string()));
    ///
    /// // The key is no longer present
    /// assert_eq!(env.get("KEY1"), None);
    ///
    /// // Removing a non-existent key returns None
    /// assert_eq!(env.remove("NONEXISTENT"), None);
    /// ```
    pub fn remove<K>(&mut self, key: K) -> Option<String>
    where
        K: AsRef<str>,
    {
        self.0.remove(key.as_ref())
    }

    /// Returns an iterator over the key-value pairs of the environment variables.
    ///
    /// The iterator element type is `(&'a String, &'a String)`.
    ///
    /// # Example
    ///
    /// ```rust
    /// use serde_envfile::Value;
    ///
    /// let env = Value::from_iter([("KEY1", "value1"), ("KEY2", "value2")]);
    ///
    /// // Iterate over key-value pairs
    /// for (key, value) in env.iter() {
    ///     println!("{} = {}", key, value);
    /// }
    /// ```
    pub fn iter(&self) -> Iter<'_> {
        Iter(self.0.iter())
    }

    /// Returns a mutable iterator over the key-value pairs of the environment variables.
    ///
    /// The iterator element type is `(&'a String, &'a mut String)`.
    ///
    /// # Example
    ///
    /// ```rust
    /// use serde_envfile::Value;
    ///
    /// let mut env = Value::from_iter([("KEY1", "value1"), ("KEY2", "value2")]);
    ///
    /// // Iterate over key-value pairs and modify values
    /// for (key, value) in env.iter_mut() {
    ///     *value = value.to_uppercase();
    ///     println!("{} = {}", key, value);
    /// }
    /// ```
    pub fn iter_mut(&mut self) -> IterMut<'_> {
        IterMut(self.0.iter_mut())
    }

    /// Removes a key from the environment variables, returning the key-value pair if the key was present.
    /// Unlike `remove()`, this method returns both the key and value as a tuple.
    ///
    /// # Example
    ///
    /// ```rust
    /// use serde_envfile::Value;
    ///
    /// let mut env = Value::from_iter([("KEY1", "VALUE1"), ("KEY2", "VALUE2")]);
    ///
    /// // Remove an existing key
    /// assert_eq!(env.remove_entry("KEY1"), Some(("KEY1".to_string(), "VALUE1".to_string())));
    ///
    /// // The key is no longer present
    /// assert_eq!(env.get("KEY1"), None);
    ///
    /// // Removing a non-existent key returns None
    /// assert_eq!(env.remove_entry("NONEXISTENT"), None);
    /// ```
    pub fn remove_entry<K>(&mut self, key: K) -> Option<(String, String)>
    where
        K: AsRef<str>,
    {
        self.0.remove_entry(key.as_ref())
    }

    /// Returns an iterator over the keys of the environment variables.
    ///
    /// The iterator element type is `&'a String`.
    ///
    /// # Example
    ///
    /// ```rust
    /// use serde_envfile::Value;
    ///
    /// let env = Value::from_iter([("KEY1", "value1"), ("KEY2", "value2")]);
    ///
    /// // Collect keys into a vector
    /// let keys: Vec<_> = env.keys().collect();
    /// for key in &keys {
    ///     println!("{}", key);
    /// }
    /// # assert!(keys.contains(&&"KEY1".to_string()));
    /// # assert!(keys.contains(&&"KEY2".to_string()));
    /// ```
    pub fn keys(&self) -> Keys<'_> {
        Keys(self.0.keys())
    }

    /// Returns an iterator over the values of the environment variables.
    ///
    /// The iterator element type is `&'a String`.
    ///
    /// # Example
    ///
    /// ```rust
    /// use serde_envfile::Value;
    ///
    /// let env = Value::from_iter([("KEY1", "value1"), ("KEY2", "value2")]);
    ///
    /// // Collect values into a vector
    /// let values: Vec<_> = env.values().collect();
    /// for value in &values {  
    ///     println!("{}", value);
    /// }
    /// # assert!(values.contains(&&"value1".to_string()));
    /// # assert!(values.contains(&&"value2".to_string()));
    /// ```
    pub fn values(&self) -> Values<'_> {
        Values(self.0.values())
    }

    /// Returns a mutable iterator over the values of the environment variables.
    ///
    /// The iterator element type is `&'a mut String`.
    ///
    /// # Example
    ///
    /// ```rust
    /// use serde_envfile::Value;
    ///
    /// let mut env = Value::from_iter([("KEY1", "value1"), ("KEY2", "value2")]);
    ///
    /// // Make all values uppercase
    /// for value in env.values_mut() {
    ///     *value = value.to_uppercase();
    /// }
    /// # assert_eq!(env.get("KEY1").unwrap(), "VALUE1");
    /// # assert_eq!(env.get("KEY2").unwrap(), "VALUE2");
    /// ```
    pub fn values_mut(&mut self) -> ValuesMut<'_> {
        ValuesMut(self.0.values_mut())
    }
}

impl std::ops::Deref for Value {
    type Target = Map<String, String>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl std::ops::DerefMut for Value {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<K, V> FromIterator<(K, V)> for Value
where
    K: Into<String>,
    V: Into<String>,
{
    /// Create a new [`Value`] from an iterator of key-value pairs.
    ///
    /// # Example
    ///
    /// ```rust
    /// use serde_envfile::Value;
    ///
    /// let env = Value::from_iter([("KEY1", "VALUE1"), ("KEY2", "VALUE2")]);
    /// # assert_eq!(env.get("KEY1").unwrap(), "VALUE1");
    /// # assert_eq!(env.get("KEY2").unwrap(), "VALUE2");
    /// ```
    fn from_iter<T: IntoIterator<Item = (K, V)>>(iter: T) -> Self {
        let iter = iter.into_iter().map(|(k, v)| (k.into(), v.into()));
        Self(FromIterator::from_iter(iter))
    }
}

impl<'a> IntoIterator for &'a Value {
    type Item = (&'a String, &'a String);
    type IntoIter = Iter<'a>;

    /// Iterate over key-value pairs in the [`Value`].
    ///
    /// # Example
    ///
    /// ```rust
    /// use serde_envfile::Value;
    ///
    /// let env = Value::from_iter([("KEY1", "VALUE1"), ("KEY2", "VALUE2")]);
    ///
    /// // Iterate over key-value pairs
    /// for (key, value) in &env {
    ///     println!("{} = {}", key, value);
    /// }
    /// ```
    fn into_iter(self) -> Self::IntoIter {
        Iter(self.0.iter())
    }
}

impl IntoIterator for Value {
    type Item = (String, String);
    type IntoIter = IntoIter;

    /// Consume the [`Value`] and iterate over owned key-value pairs.
    ///
    /// # Example
    ///
    /// ```rust
    /// use serde_envfile::Value;
    ///
    /// let env = Value::from_iter([("KEY1", "VALUE1"), ("KEY2", "VALUE2")]);
    ///
    /// // Consume the Value and iterate over owned key-value pairs
    /// for (key, value) in env {
    ///     println!("{} = {}", key, value);
    /// }
    /// ```
    fn into_iter(self) -> Self::IntoIter {
        IntoIter(self.0.into_iter())
    }
}

impl<K, V> Extend<(K, V)> for Value
where
    K: Into<String>,
    V: Into<String>,
{
    /// Extend the [`Value`] with key-value pairs from another iterator.
    ///
    /// # Example
    ///
    /// ```rust
    /// use serde_envfile::Value;
    ///
    /// let mut env = Value::from_iter([("KEY1", "VALUE1")]);
    ///
    /// // Extend with additional key-value pairs
    /// env.extend([("KEY2", "VALUE2"), ("KEY3", "VALUE3")]);
    /// # assert_eq!(env.get("KEY1").unwrap(), "VALUE1");
    /// # assert_eq!(env.get("KEY2").unwrap(), "VALUE2");
    /// # assert_eq!(env.get("KEY3").unwrap(), "VALUE3");
    /// ```
    fn extend<T: IntoIterator<Item = (K, V)>>(&mut self, iter: T) {
        self.0
            .extend(iter.into_iter().map(|(k, v)| (k.into(), v.into())));
    }
}

impl<'a> IntoIterator for &'a mut Value {
    type Item = (&'a String, &'a mut String);
    type IntoIter = IterMut<'a>;

    /// Iterate mutably over key-value pairs in the [`Value`].
    ///
    /// # Example
    ///
    /// ```rust
    /// use serde_envfile::Value;
    ///
    /// let mut env = Value::from_iter([("KEY1", "value1"), ("KEY2", "value2")]);
    ///
    /// // Iterate mutably over key-value pairs and make values uppercase
    /// for (_, value) in &mut env {
    ///     *value = value.to_uppercase();
    /// }
    /// # assert_eq!(env.get("KEY1").unwrap(), "VALUE1");
    /// # assert_eq!(env.get("KEY2").unwrap(), "VALUE2");
    /// ```
    fn into_iter(self) -> Self::IntoIter {
        IterMut(self.0.iter_mut())
    }
}

/// An iterator that takes ownership of key-value pairs.
///
/// Created by calling [`into_iter`] on a [`Value`].
#[derive(Debug)]
pub struct IntoIter(InnerIntoIter<String, String>);

impl Iterator for IntoIter {
    type Item = (String, String);

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl ExactSizeIterator for IntoIter {
    fn len(&self) -> usize {
        self.0.len()
    }
}

/// An iterator over key-value pairs by reference.
///
/// Created by calling [`iter`] on a [`Value`] or using the [`IntoIterator`] implementation on a reference.
#[derive(Debug)]
pub struct Iter<'a>(InnerIter<'a, String, String>);

impl<'a> Iterator for Iter<'a> {
    type Item = (&'a String, &'a String);

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl ExactSizeIterator for Iter<'_> {
    fn len(&self) -> usize {
        self.0.len()
    }
}

/// An iterator over key-value pairs with mutable value references.
///
/// Created by calling [`iter_mut`] on a [`Value`] or using the [`IntoIterator`] implementation on a mutable reference.
/// The iterator yields a reference to the key and a mutable reference to the value.
#[derive(Debug)]
pub struct IterMut<'a>(InnerIterMut<'a, String, String>);

impl<'a> Iterator for IterMut<'a> {
    type Item = (&'a String, &'a mut String);

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl ExactSizeIterator for IterMut<'_> {
    fn len(&self) -> usize {
        self.0.len()
    }
}

/// An iterator over the keys of a [`Value`].
///
/// This struct is created by the [`keys`] method on [`Value`].
/// See its documentation for more.
#[derive(Debug)]
pub struct Keys<'a>(InnerKeys<'a, String, String>);

impl<'a> Iterator for Keys<'a> {
    type Item = &'a String;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl ExactSizeIterator for Keys<'_> {
    fn len(&self) -> usize {
        self.0.len()
    }
}

/// An iterator over the values of a [`Value`].
///
/// This struct is created by the [`values`] method on [`Value`].
/// See its documentation for more.
#[derive(Debug)]
pub struct Values<'a>(InnerValues<'a, String, String>);

impl<'a> Iterator for Values<'a> {
    type Item = &'a String;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl ExactSizeIterator for Values<'_> {
    fn len(&self) -> usize {
        self.0.len()
    }
}

/// A mutable iterator over the values of a [`Value`].
///
/// This struct is created by the [`values_mut`] method on [`Value`].
/// See its documentation for more.
#[derive(Debug)]
pub struct ValuesMut<'a>(InnerValuesMut<'a, String, String>);

impl<'a> Iterator for ValuesMut<'a> {
    type Item = &'a mut String;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl ExactSizeIterator for ValuesMut<'_> {
    fn len(&self) -> usize {
        self.0.len()
    }
}

#[cfg(test)]
mod tests {
    use super::Value;
    use crate::{de::from_str, ser::to_string};

    #[test]
    fn value_to_string() {
        //* Given
        let env = Value::from_iter([("KEY1", "VALUE1"), ("KEY2", "VALUE2")]);

        //* When
        let value_serialized = to_string(&env).expect("Failed to convert Value to String");
        let value_deserialized =
            from_str::<Value>(&value_serialized).expect("Failed to deserialize Value");

        //* Then
        // Assert that both expected lines are present
        // The order of keys in the serialized output is not guaranteed without the `preserve_order` feature
        assert!(value_serialized.contains(r#"KEY1="VALUE1""#));
        assert!(value_serialized.contains(r#"KEY2="VALUE2""#));

        // Assert the deserialize output follows the order of the original input
        // when the `preserve_order` feature is enabled
        #[cfg(feature = "preserve_order")]
        {
            let expected_serialized = "KEY1=\"VALUE1\"\nKEY2=\"VALUE2\"";
            assert_eq!(value_serialized, expected_serialized);
        }

        // Create a new Value with lowercase keys to match the deserialization behavior
        let expected_deserialized = Value::from_iter([("key1", "VALUE1"), ("key2", "VALUE2")]);
        assert_eq!(value_deserialized, expected_deserialized);
    }

    #[test]
    fn value_iter_ref_collects_correctly() {
        //* Given
        let env = Value::from_iter([("KEY1", "VALUE1"), ("KEY2", "VALUE2")]);

        //* When
        let ref_items = (&env).into_iter().collect::<Vec<_>>();

        //* Then
        assert_eq!(ref_items.len(), 2);
        assert!(ref_items.contains(&(&"KEY1".to_string(), &"VALUE1".to_string())));
        assert!(ref_items.contains(&(&"KEY2".to_string(), &"VALUE2".to_string())));

        // Assert the iteration order is correct, when the `preserve_order` feature is enabled
        #[cfg(feature = "preserve_order")]
        {
            assert_eq!(ref_items[0], (&"KEY1".to_string(), &"VALUE1".to_string()));
            assert_eq!(ref_items[1], (&"KEY2".to_string(), &"VALUE2".to_string()));
        }
    }

    #[test]
    fn value_iter_owned_collects_correctly() {
        //* Given
        let env = Value::from_iter([("KEY1", "VALUE1"), ("KEY2", "VALUE2")]);

        //* When
        let owned_items = env.into_iter().collect::<Vec<_>>();

        //* Then
        assert_eq!(owned_items.len(), 2);
        assert!(owned_items.contains(&("KEY1".to_string(), "VALUE1".to_string())));
        assert!(owned_items.contains(&("KEY2".to_string(), "VALUE2".to_string())));

        // Assert the iteration order is correct, when the `preserve_order` feature is enabled
        #[cfg(feature = "preserve_order")]
        {
            assert_eq!(owned_items[0], ("KEY1".to_string(), "VALUE1".to_string()));
            assert_eq!(owned_items[1], ("KEY2".to_string(), "VALUE2".to_string()));
        }
    }

    #[test]
    fn value_iter_size_hint_is_correct() {
        //* Given
        let env = Value::from_iter([("KEY1", "VALUE1"), ("KEY2", "VALUE2")]);

        //* When
        let iter = env.into_iter();

        //* Then
        assert_eq!(iter.size_hint(), (2, Some(2)));
    }

    #[test]
    fn value_iter_ref_size_hint_is_correct() {
        //* Given
        let env = Value::from_iter([("KEY1", "VALUE1"), ("KEY2", "VALUE2")]);

        //* When
        let ref_iter = (&env).into_iter();

        //* Then
        assert_eq!(ref_iter.size_hint(), (2, Some(2)));
    }

    #[test]
    fn value_iter_mut_modifies_values() {
        //* Given
        let mut env = Value::from_iter([("KEY1", "value1"), ("KEY2", "value2")]);

        //* When
        for (_, value) in &mut env {
            *value = value.to_uppercase();
        }

        //* Then
        assert_eq!(env.get("KEY1").unwrap(), "VALUE1");
        assert_eq!(env.get("KEY2").unwrap(), "VALUE2");

        // Assert the iteration order is preserved, when the `preserve_order` feature is enabled
        #[cfg(feature = "preserve_order")]
        {
            let pairs = env.into_iter().collect::<Vec<_>>();
            assert_eq!(pairs[0], ("KEY1".to_string(), "VALUE1".to_string()));
            assert_eq!(pairs[1], ("KEY2".to_string(), "VALUE2".to_string()));
        }
    }

    #[test]
    fn value_iter_mut_size_hint_is_correct() {
        //* Given
        let mut env = Value::from_iter([("KEY1", "VALUE1"), ("KEY2", "VALUE2")]);

        //* When
        let iter = (&mut env).into_iter();

        //* Then
        assert_eq!(iter.size_hint(), (2, Some(2)));
    }

    #[test]
    fn value_keys_returns_all_keys() {
        //* Given
        let env = Value::from_iter([("KEY1", "value1"), ("KEY2", "value2")]);

        //* When
        let keys = env.keys().collect::<Vec<_>>();

        //* Then
        assert_eq!(keys.len(), 2);
        assert!(keys.contains(&&String::from("KEY1")));
        assert!(keys.contains(&&String::from("KEY2")));

        // Assert the iteration order is preserved, when the `preserve_order` feature is enabled
        #[cfg(feature = "preserve_order")]
        {
            assert_eq!(keys[0], &String::from("KEY1"));
            assert_eq!(keys[1], &String::from("KEY2"));
        }
    }

    #[test]
    fn value_keys_size_hint_is_correct() {
        //* Given
        let env = Value::from_iter([("KEY1", "VALUE1"), ("KEY2", "VALUE2")]);

        //* When
        let iter = env.keys();

        //* Then
        assert_eq!(iter.size_hint(), (2, Some(2)));
    }

    #[test]
    fn value_values_returns_all_values() {
        //* Given
        let env = Value::from_iter([("KEY1", "value1"), ("KEY2", "value2")]);

        //* When
        let values = env.values().collect::<Vec<_>>();

        //* Then
        assert_eq!(values.len(), 2);
        assert!(values.contains(&&String::from("value1")));
        assert!(values.contains(&&String::from("value2")));

        // Assert the iteration order is preserved, when the `preserve_order` feature is enabled
        #[cfg(feature = "preserve_order")]
        {
            assert_eq!(values[0], &String::from("value1"));
            assert_eq!(values[1], &String::from("value2"));
        }
    }

    #[test]
    fn value_values_size_hint_is_correct() {
        //* Given
        let env = Value::from_iter([("KEY1", "VALUE1"), ("KEY2", "VALUE2")]);

        //* When
        let iter = env.values();

        //* Then
        assert_eq!(iter.size_hint(), (2, Some(2)));
    }

    #[test]
    fn value_values_mut_modifies_values() {
        //* Given
        let mut env = Value::from_iter([("KEY1", "value1"), ("KEY2", "value2")]);

        //* When
        for value in env.values_mut() {
            *value = value.to_uppercase();
        }

        //* Then
        assert_eq!(env.get("KEY1").unwrap(), "VALUE1");
        assert_eq!(env.get("KEY2").unwrap(), "VALUE2");

        // Assert the iteration order is preserved, when the `preserve_order` feature is enabled
        #[cfg(feature = "preserve_order")]
        {
            let pairs = env.into_iter().collect::<Vec<_>>();
            assert_eq!(pairs[0], ("KEY1".to_string(), "VALUE1".to_string()));
            assert_eq!(pairs[1], ("KEY2".to_string(), "VALUE2".to_string()));
        }
    }

    #[test]
    fn value_values_mut_size_hint_is_correct() {
        //* Given
        let mut env = Value::from_iter([("KEY1", "VALUE1"), ("KEY2", "VALUE2")]);

        //* When
        let iter = env.values_mut();

        //* Then
        assert_eq!(iter.size_hint(), (2, Some(2)));
    }
}
