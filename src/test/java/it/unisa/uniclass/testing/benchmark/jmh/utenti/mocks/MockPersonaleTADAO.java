package it.unisa.uniclass.testing.benchmark.jmh.utenti.mocks;

import it.unisa.uniclass.utenti.model.PersonaleTA;

import java.util.*;

public class MockPersonaleTADAO implements PersonaleTARemote {

    // archivio interno più realistico
    private final Map<String, PersonaleTA> byEmail = new HashMap<>();
    private PersonaleTA personaleDaRitornare;

    public void add(PersonaleTA p) {
        byEmail.put(p.getEmail(), p);
    }
    // Questo metodo deve essere visibile
    public void setPersonaleDaRitornare(PersonaleTA p) {
        this.personaleDaRitornare = p;
    }
    public void clear() {
        byEmail.clear();
    }

    @Override
    public PersonaleTA trovaEmail(String email) {
        if (personaleDaRitornare != null && email.equals(personaleDaRitornare.getEmail())) {
            return personaleDaRitornare;
        }
        return byEmail.getOrDefault(email, null);
    }

    @Override
    public PersonaleTA trovaEmailPassword(String email, String password) {
        if (personaleDaRitornare != null &&
            email.equals(personaleDaRitornare.getEmail()) &&
            Objects.equals(password, personaleDaRitornare.getPassword())) {
            return personaleDaRitornare;
        }
        PersonaleTA p = byEmail.get(email);
        if (p != null && Objects.equals(p.getPassword(), password)) {
            return p;
        }
        return null;
    }

    @Override
    public PersonaleTA trovaPersonale(long id) {
        return null;
    }

    @Override
    public List<PersonaleTA> trovaTutti() {
        if (personaleDaRitornare != null) {
            return Collections.singletonList(personaleDaRitornare);
        }
        return new ArrayList<>(byEmail.values());
    }

    @Override
    public void aggiungiPersonale(PersonaleTA p) { }

    @Override
    public void rimuoviPersonale(PersonaleTA p) { }
}
