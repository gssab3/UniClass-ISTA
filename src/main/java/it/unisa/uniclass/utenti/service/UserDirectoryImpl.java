package it.unisa.uniclass.utenti.service;

import it.unisa.uniclass.common.exceptions.NotFoundUserException;
import it.unisa.uniclass.utenti.model.Accademico;
import it.unisa.uniclass.utenti.model.Ruolo;
import it.unisa.uniclass.utenti.model.Utente;
import jakarta.ejb.EJB;
import jakarta.ejb.Stateless;
import it.unisa.uniclass.utenti.*;

@Stateless
public class UserDirectoryImpl implements UserDirectory {

    @EJB
    private UtenteService utenteService;

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
        return a != null && a.getRuolo() == Ruolo.Docente;
    }

    @Override
    public boolean isStudente(String email) {
        Accademico a = getAccademico(email);
        return a != null && a.getRuolo() == Ruolo.Studente;
    }
}