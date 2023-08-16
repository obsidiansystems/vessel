# Revision history for vessel

## Unreleased

* Add flag for enabling/disabling tutorial build

## 0.3.0.0-r1

* Loosen reflex bounds

## 0.3.0.0

* Fix singleV: absent query /= present query for deleted item
* Use Commutative instead of the deprecated Additive
* Update for constraints-extras 0.4

## 0.2.1.0

* Allow `Vessel` and `DMapV` types to be more liberally kinded in their indexes.
* Add Data.Vessel.Path. See that module for documentation.
* Add `singletonDMapV` and `lookupDMapV`

## 0.2.0.0

* Add an orphan instance for 'Additive' of 'Compose' this is in line with the other orphans for 'Compose' that will be phased out in a future release in favor of an upstream solution.

## 0.1.0.0

* Initial release
