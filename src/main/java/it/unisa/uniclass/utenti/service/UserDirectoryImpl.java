package it.unisa.uniclass.utenti.service;

import it.unisa.uniclass.common.exceptions.AuthenticationException;
import it.unisa.uniclass.common.exceptions.NotFoundUserException;
import it.unisa.uniclass.utenti.model.Accademico;
import it.unisa.uniclass.utenti.model.Ruolo;
import it.unisa.uniclass.utenti.model.Utente;
import jakarta.ejb.EJB;
import jakarta.ejb.Stateless;

import java.util.List;

@Stateless
public class UserDirectoryImpl implements UserDirectory {

    // DIPENDENZA: UserDirectory dipende da UtenteService per il lavoro sporco
    @EJB
    private UtenteService utenteService;

    @Override
    public Utente login(String email, String password) throws AuthenticationException {
        return utenteService.login(email, password);
    }

    @Override
    public Utente getUser(String email) {
        try {
            return utenteService.getUtenteByEmail(email);
        } catch (NotFoundUserException e) {
            return null;
        }
    }

    @Override
    public Accademico getAccademico(String email) {
        Utente u = getUser(email);
        if (u instanceof Accademico) {
            return (Accademico) u;
        }
        return null;
    }

    @Override
    public boolean isDocente(String email) {
        Accademico a = getAccademico(email);
        return a != null && a.getRuolo() == Ruolo.DOCENTE;
    }

    @Override
    public boolean isStudente(String email) {
        Accademico a = getAccademico(email);
        return a != null && a.getRuolo() == Ruolo.STUDENTE;
    }

    @Override
    public boolean isCoordinatore(String email) {
        Accademico a = getAccademico(email);
        return a != null && a.getRuolo() == Ruolo.COORDINATORE;
    }

    @Override
    public List<Utente> getTuttiGliUtenti() {
        return utenteService.getTuttiGliUtenti();
    }

    @Override
    public List<Accademico> getAccademiciPerRuolo(Ruolo ruolo) {
        // Delega al service che ha accesso ai DAO specifici
        return utenteService.getAccademiciPerRuolo(ruolo);
    }

    @Override
    public void updateProfile(Utente utente) {
        utenteService.aggiornaUtente(utente);
    }

    @Override
    public void cambiaStatoAttivazione(String email, boolean stato) {
        Utente u = getUser(email);
        if (u instanceof Accademico) {
            Accademico acc = (Accademico) u;
            acc.setAttivato(stato);
            utenteService.aggiornaUtente(acc);
        }
    }
}