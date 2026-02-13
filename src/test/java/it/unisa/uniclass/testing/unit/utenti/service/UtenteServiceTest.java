package it.unisa.uniclass.testing.unit.utenti.service;


import it.unisa.uniclass.common.exceptions.AlreadyExistentUserException;
import it.unisa.uniclass.common.exceptions.AuthenticationException;
import it.unisa.uniclass.common.exceptions.NotFoundUserException;
import it.unisa.uniclass.utenti.model.Accademico;
import it.unisa.uniclass.utenti.model.Ruolo;
import it.unisa.uniclass.utenti.model.Tipo;
import it.unisa.uniclass.utenti.model.Utente;
import it.unisa.uniclass.utenti.service.UtenteService;
import it.unisa.uniclass.utenti.service.dao.AccademicoRemote;
import it.unisa.uniclass.utenti.service.dao.UtenteRemote;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

class UtenteServiceTest {

    @Test
    void login_shouldReturnUser_whenCredentialsValid() throws Exception {
        UtenteRemote utenteDAO = mock(UtenteRemote.class);
        AccademicoRemote accademicoDAO = mock(AccademicoRemote.class);
        UtenteService service = new UtenteService(utenteDAO, accademicoDAO);

        Utente u = new Utente();
        when(utenteDAO.login("a", "b")).thenReturn(u);

        assertEquals(u, service.login("a", "b"));
    }

    @Test
    void login_shouldThrowException_whenCredentialsInvalid() {
        UtenteRemote utenteDAO = mock(UtenteRemote.class);
        AccademicoRemote accademicoDAO = mock(AccademicoRemote.class);
        UtenteService service = new UtenteService(utenteDAO, accademicoDAO);

        when(utenteDAO.login("a", "b")).thenReturn(null);

        assertThrows(AuthenticationException.class, () -> service.login("a", "b"));
    }

    @Test
    void registraUtente_shouldThrowException_whenEmailExists() {
        UtenteRemote utenteDAO = mock(UtenteRemote.class);
        AccademicoRemote accademicoDAO = mock(AccademicoRemote.class);
        UtenteService service = new UtenteService(utenteDAO, accademicoDAO);

        Utente u = new Utente();
        u.setEmail("x");

        when(utenteDAO.findByEmail("x")).thenReturn(new Utente());

        assertThrows(AlreadyExistentUserException.class, () -> service.registraUtente(u));
    }

    @Test
    void registraUtente_shouldCreateUser_whenEmailNotExists() throws Exception {
        UtenteRemote utenteDAO = mock(UtenteRemote.class);
        AccademicoRemote accademicoDAO = mock(AccademicoRemote.class);
        UtenteService service = new UtenteService(utenteDAO, accademicoDAO);

        Utente u = new Utente();
        u.setEmail("x");

        when(utenteDAO.findByEmail("x")).thenReturn(null);

        service.registraUtente(u);

        assertEquals(Tipo.Accademico, u.getTipo());
        verify(utenteDAO).create(u);
    }

    @Test
    void registraAccademico_shouldThrowException_whenEmailExists() {
        UtenteRemote utenteDAO = mock(UtenteRemote.class);
        AccademicoRemote accademicoDAO = mock(AccademicoRemote.class);
        UtenteService service = new UtenteService(utenteDAO, accademicoDAO);

        Accademico a = new Accademico();
        a.setEmail("x");

        when(utenteDAO.findByEmail("x")).thenReturn(new Utente());

        assertThrows(AlreadyExistentUserException.class, () -> service.registraAccademico(a, Ruolo.DOCENTE));
    }

    @Test
    void registraAccademico_shouldCreateAccademico_whenEmailNotExists() throws Exception {
        UtenteRemote utenteDAO = mock(UtenteRemote.class);
        AccademicoRemote accademicoDAO = mock(AccademicoRemote.class);
        UtenteService service = new UtenteService(utenteDAO, accademicoDAO);

        Accademico a = new Accademico();
        a.setEmail("x");

        when(utenteDAO.findByEmail("x")).thenReturn(null);

        service.registraAccademico(a, Ruolo.DOCENTE);

        assertEquals(Ruolo.DOCENTE, a.getRuolo());
        verify(accademicoDAO).create(a);
    }

    @Test
    void getUtenteByEmail_shouldReturnUser_whenFound() throws Exception {
        UtenteRemote utenteDAO = mock(UtenteRemote.class);
        AccademicoRemote accademicoDAO = mock(AccademicoRemote.class);
        UtenteService service = new UtenteService(utenteDAO, accademicoDAO);

        Utente u = new Utente();
        when(utenteDAO.findByEmail("x")).thenReturn(u);

        assertEquals(u, service.getUtenteByEmail("x"));
    }

    @Test
    void getUtenteByEmail_shouldThrowException_whenNotFound() {
        UtenteRemote utenteDAO = mock(UtenteRemote.class);
        AccademicoRemote accademicoDAO = mock(AccademicoRemote.class);
        UtenteService service = new UtenteService(utenteDAO, accademicoDAO);

        when(utenteDAO.findByEmail("x")).thenReturn(null);

        assertThrows(NotFoundUserException.class, () -> service.getUtenteByEmail("x"));
    }

    @Test
    void aggiornaUtente_shouldUpdateAccademico_whenInstanceOfAccademico() {
        UtenteRemote utenteDAO = mock(UtenteRemote.class);
        AccademicoRemote accademicoDAO = mock(AccademicoRemote.class);
        UtenteService service = new UtenteService(utenteDAO, accademicoDAO);

        Accademico a = new Accademico();

        service.aggiornaUtente(a);

        verify(accademicoDAO).update(a);
        verify(utenteDAO, never()).update(any());
    }

    @Test
    void aggiornaUtente_shouldUpdateUtente_whenNotAccademico() {
        UtenteRemote utenteDAO = mock(UtenteRemote.class);
        AccademicoRemote accademicoDAO = mock(AccademicoRemote.class);
        UtenteService service = new UtenteService(utenteDAO, accademicoDAO);

        Utente u = new Utente();

        service.aggiornaUtente(u);

        verify(utenteDAO).update(u);
        verify(accademicoDAO, never()).update(any());
    }
}

